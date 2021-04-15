import tables, strutils, sequtils, deques
from sugar import `=>`, `->`, dump
from terminal import getch

type
  #Stack = Deque[uint16]
  Stack = object
    data: array[1024, Cell]
    pos: Natural
  Forth = object
    data: Stack
    ret: Stack
    dict: TableRef[string, (f: var Forth) -> void]
    mem: Memory
    show: bool
    compileConstruct: CompileConstruct
    runState: Deque[RunState]

  Word = uint16
  DoubleWord = array[2, Word]

  Memory = object
    pos: Natural
    buf: array[1024, byte]

  CellType {.size: 1, pure.} = enum
    data memory

  Cell = object {.packed.}
    case kind: CellType
    of CellType.data:
      data: uint16
    of CellType.memory:
      pos: uint16

  StackError = object of CatchableError

  RunState = enum
    rsInterpret rsCompile rsComment rsHalt rsString

  TokenType {.pure.} = enum
    data word `if` `else` then noop loop `do` `string`

  TokenObject = object
    case kind: TokenType
    of TokenType.data:
      data: Cell
    of TokenType.word:
      word: string
    of TokenType.string:
      mempos: uint16
    of TokenType.if, TokenType.else, TokenType.then, TokenType.noop,
      TokenType.do, TokenType.loop:
      discard

  CompileConstruct = object
    name: string
    construct: seq[TokenObject]

converter toU16(c: Cell): uint16 =
  if c.kind == CellType.data:
    result = c.data

converter toCell(u: uint16): Cell =
  result = Cell(kind: CellType.data, data: u)

template `as`(a, b: untyped): untyped =
  cast[`b`](`a`)

proc initTokenObject(kind: TokenType): TokenObject =
  const spectypes ={ TokenType.if, TokenType.then, TokenType.loop,
    TokenType.else, TokenType.do}
  if kind notin spectypes:
    result = TokenObject(kind: TokenType.noop)
  else:
    result = TokenObject(kind: kind)

proc initTokenObject[T: uint16|string|Cell](data: T): TokenObject =
  when T is uint16:
    result = TokenObject(
      kind: TokenType.data,
      data: data)
  elif T is Cell:
    result = TokenObject(
      kind: TokenType.string,
      mempos: data.pos)
  elif T is string:
    result = TokenObject(
      kind: TokenType.word,
      word: data)

proc initStack(cap = 1024): Stack =
  #initDeque[uint16]()
  Stack()

proc len(s: Stack): int = s.pos

proc `[]`(s: Stack, index: Natural): Cell = s.data[s.pos-index]
#proc `[]=`(s: var Stack, pos: Natural, val: uint16) = s.data[pos] = val

proc addFirst[T: Cell | uint16](s: var Stack, val: T) =
  if s.pos >= s.data.high:
    echo "Not enough capacity"
    return
  inc s.pos
  when T is uint16:
    s.data[s.pos] = Cell(kind: CellType.data, data: val)
  else:
    s.data[s.pos] = val

proc popFirst(s: var Stack): Cell =
  if s.pos <= 0:
    raise newException(StackError, "Empty stack")
  result = s.data[s.pos]
  dec s.pos

proc pop(stack: var Stack): (Cell, StackError) =
  try:
    let v = stack.popFirst
    result = (v, StackError())
  except:
    let e = getCurrentException()
    result = (Cell(), StackError(name: "StackError", msg: e.msg))

proc push[T: Cell|uint16](stack: var Stack, value: T): (bool, StackError) =
  stack.addFirst value
  result = (true, StackError())

proc register(f: var Forth, word: string, prc: proc(f: var Forth)) =
  f.dict[word] = prc

template handleErr(err: StackError): untyped =
  if err.msg != "":
    echo err.msg
    return

template checkArity(f: Forth, n: int): untyped =
  if f.data.len < n:
    echo "insufficient stack"
    return

template checkBinary(f: Forth): untyped =
  checkArity(f, 2)

template checkTriplet(f: Forth): untyped =
  checkArity(f, 3)

template forthArith(f: var Forth, op: untyped, booleanop = false): untyped =
  checkBinary f
  let (top, err) = f.data.pop
  handleErr err
  let topcast = top.toU16 as int16
  let (top2, err2) = f.data.pop
  handleErr err2
  let top2cast = top2.toU16 as int16
  when booleanop:
    let value = `op`(top2cast, topcast)
    var boolval = if (value as bool): -1'i16 else: 0'i16
    let (_, err3) = f.data.push(boolval as uint16)
    handleErr err3
  else:
    let value: int32 = `op`(top2cast as int32, topcast as int32)
    if value > int16.high or value < int16.low:
      let data = value as uint32 as DoubleWord
      for i in countdown(data.high, 0):
        discard f.data.push(data[i])
    else:
      let (_, err3) = f.data.push(value as uint16)
      handleErr err3

proc addForth(f: var Forth) =
  forthArith(f, `+`)

proc negForth(f: var Forth) =
  forthArith(f, `-`)

proc mulForth(f: var Forth) =
  forthArith(f, `*`)

proc divForth(f: var Forth) =
  forthArith(f, `div`)

proc isNumber(token: string): bool =
  if token.len > 1 and token[0] == '-' and token[1 .. ^1].all(isDigit):
    true
  elif token.len > 0 and token.all(isDigit):
    true
  else:
    false

proc showTop(f: var Forth) =
  checkArity f, 1
  let (v, err) = f.data.pop
  handleErr err

  case v.kind
  of CellType.data:
    stdout.write(v.data as int16, ' ')
  of CellType.memory:
    let thelen = f.mem.buf[v.pos]
    for i in 1.byte .. thelen:
      stdout.write(f.mem.buf[v.pos+i].char)
    stdout.write ' '
    f.mem.pos = v.pos
    #[
    var pos = f.mem.pos - Natural(thelen+1)
    if pos < 0:
      pos = 0
    f.mem.pos = 0
    ]#
  f.show = true

proc showTopDouble(f: var Forth) =
  let (p1, err1) = f.data.pop
  handleErr err1
  let (p2, err2) = f.data.pop
  handleErr err2
  let p = [p1.toU16, p2.toU16] as uint32
  stdout.write(p as int32, ' ')
  f.show = true

proc showTopQuad(f: var Forth) =
  var data: array[4, uint16]
  for i in 0 .. 3:
    let (someval, err) = f.data.pop
    data[i] = someval.toU16
    handleErr err
  let p = data as uint64

  stdout.write(p as int64,' ')
  f.show = true

proc showStack(f: var Forth) =
  if f.data.len == 0:
    stdout.write "[] "
  else:
    stdout.write "[ "
    for i in countdown(f.data.len-1, 0):
      let cell = f.data[i]
      case cell.kind
      of CellType.data:
        stdout.write(cell.data, ' ')
      of CellType.memory:
        stdout.write("memory:", cell.pos, ' ')
    stdout.write "] "
  f.show = true

proc dup(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  for i in 1 .. 2:
    discard f.data.push v

template retrieveBinary(f: var Forth): untyped {.dirty.} =
  let (v1, err) = f.data.pop
  handleErr err
  let (v2, err2) = f.data.pop
  handleErr err2

proc swap(f: var Forth) =
  checkBinary f
  retrieveBinary f
  discard f.data.push v1
  discard f.data.push v2

proc over(f: var Forth) =
  checkBinary f
  let v = f.data[1]
  discard f.data.push v

proc rot(f: var Forth) =
  checkTriplet f
  retrieveBinary f
  let (v3, err3) = f.data.pop
  handleErr err3
  discard f.data.push v2
  discard f.data.push v1
  discard f.data.push v3

template retrieveBinaryDouble(f: var Forth): untyped {.dirty.} =
  let (p11, err11) = f.data.pop
  handleErr err11
  let (p12, err12) = f.data.pop
  handleErr err12
  let (p21, err21) = f.data.pop
  handleErr err21
  let (p22, err22) = f.data.pop
  handleErr err22

proc swapDouble(f: var Forth) =
  checkArity f, 4
  retrieveBinaryDouble f
  discard f.data.push p11
  discard f.data.push p12
  discard f.data.push p21
  discard f.data.push p22

proc overDouble(f: var Forth) =
  checkArity f, 4
  let v1 = f.data[2]
  let v2 = f.data[3]
  discard f.data.push v2
  discard f.data.push v1

proc dupDouble(f: var Forth) =
  checkBinary f
  let (p1, err1) = f.data.pop
  handleErr err1
  let (p2, err2) = f.data.pop
  handleErr err2
  discard f.data.push p2
  discard f.data.push p1
  discard f.data.push p2
  discard f.data.push p1

proc dupQuad(f: var Forth) =
  checkArity f, 8
  var data: array[4, uint16]
  for i in 0 .. 3:
    var err: StackError
    (data[i], err) = f.data.pop
    handleErr err
  for _ in 1 .. 2:
    for i in countdown(3, 0):
      discard f.data.push data[i]

proc dropDouble(f: var Forth) =
  checkBinary f
  discard f.data.pop
  discard f.data.pop

template forthArithDouble(f: var Forth, op: untyped, booleanop = false): untyped =
  checkArity f, 4
  retrieveBinaryDouble f
  let p1 = [p11.toU16, p12.toU16] as uint32
  let p2 = [p21.toU16, p22.toU16] as uint32
  let val = `op`(p2 as int32, p1 as int32)
  if booleanop:
    discard f.data.push(if bool(val): -1 as uint16 else: 0)
  else:
    let data = (val as uint32) as DoubleWord
    for i in countdown(data.high, 0):
      discard f.data.push data[i]

proc divmod(f: var Forth) =
  checkBinary f
  retrieveBinary f
  let v1i = v1.toU16 as int16
  let v2i = v2.toU16 as int16
  let rem = v2i mod v1i
  let quot = v2i div v1i
  discard f.data.push(rem  as uint16)
  discard f.data.push(quot as uint16)

template handleString(line: string, start = 0): (bool, string) =
  var r = (false, "")
  if start != -1:
    var pos = line.find('"', start = start)
    if pos == -1:
      r = (false, line[start .. ^1])
    elif pos != 0 and line[pos-1] != '\\':
      r = (true, line[start .. pos])
  r

proc spaces(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  for _ in 1'u16 .. v:
    stdout.write ' '
  f.show = true

proc emit(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  stdout.write chr(v.toU16)
  f.show = true

proc drop(f: var Forth) =
  let (_, err) = f.data.pop
  handleErr err

proc constructBody(f: var Forth, cc: CompileConstruct) =
  dump cc
  var isTrue = true
  var isLoop = false
  var idx = 0
  var lastjumpIdx = initDeque[int]()
  var lastLoopCount = initDeque[int16]()
  #for idx, obj in cc.construct:
  while idx <= cc.construct.high:
    let obj = cc.construct[idx]
    case obj.kind
    of TokenType.data:
      if isTrue:
        discard f.data.push obj.data
    of TokenType.string:
      if isTrue:
        discard f.data.push(Cell(kind: CellType.memory, pos: obj.mempos))
    of TokenType.word:
      if f.dict.hasKey(obj.word) and isTrue:
        f.dict[obj.word](f)
    of TokenType.if:
      let (testTrue, err) = f.data.pop
      handleErr err
      let trueTrue = testTrue.toU16 as int16
      isTrue = trueTrue == -1
    of TokenType.else:
      isTrue = not isTrue
    of TokenType.then:
      isTrue = true
    of TokenType.do:
      if isTrue:
        lastjumpIdx.addFirst idx
        let (looping, err) = f.data.pop
        handleErr err
        let loopTime = looping.toU16 as int16
        lastLoopCount.addFirst loopTime
    of TokenType.loop:
      if isTrue:
        if lastjumpIdx.len > 0 and lastLoopCount.len > 0:
          var count = lastLoopCount.popFirst
          if count > 1:
            idx = lastjumpIdx[0]
            dec count
            lastLoopCount.addFirst count
          else:
            discard lastjumpIdx.popFirst
        
    of TokenType.noop:
      discard

    inc idx

proc constructDef(vm: var Forth) =
  let cc = vm.compileConstruct
  var closure = proc(f: var Forth) = f.constructBody cc
  vm.register(vm.compileConstruct.name, closure)

proc putData(vm: var Forth, val: int, runState: RunState) =
  template addTo(n: static[int], isCompiled: static[bool], typ: typedesc) =
    let data = (val as typ) as array[n, uint16]
    for i in countdown(data.high, 0):
      when isCompiled:
        vm.compileConstruct.construct.add initTokenObject(data[i])
      else:
        discard vm.data.push data[i]

  if runState == rsCompile:
    if val < int32.low or val > int32.high:
      addTo(4, true, uint64)
    elif val < int16.low or val > int16.high:
      addTo(2, true, uint32)
    else:
      vm.compileConstruct.construct.add initTokenObject(val as uint16)
  else:
    if val < int32.low or val > int32.high:
      addTo(4, false, uint64)
    elif val < int16.low or val > int16.high:
      addTo(2, false, uint64)
    else:
      discard vm.data.push(val as uint16)

proc toDouble(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  let vv = (v.toU16) as int16 as int32 as uint32 as DoubleWord
  for i in countdown(vv.high, 0):
    discard f.data.push vv[i]

template constructIfThen(f: var Forth, kind: TokenType): untyped =
  if f.runState == rsCompile and f.compileConstruct.name != "":
    f.compileConstruct.construct.add initTokenObject(kind)

template ifthenConstruct(f: Forth, target, token: string): bool =
  target == token and f.compileConstruct.name != "" and f.runState[0] == rsCompile

proc toR(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  discard f.ret.push v

proc fromR(f: var Forth) =
  let (v, err) = f.ret.pop
  handleErr err
  discard f.data.push v

proc iR(f: var Forth) =
  if f.ret.len < 1:
    echo "insufficient return stack"
    return
  discard f.ret.push f.ret[0]

proc jR(f: var Forth) =
  if f.ret.len < 3:
    echo "insufficient return stack"
    return
  discard f.ret.push f.ret[2]


template registration(vm: var Forth): untyped =
  vm.register("+", addForth)
  vm.register("-", negForth)
  vm.register("/", divForth)
  vm.register("*", mulForth)
  vm.register(">", (f: var Forth) => forthArith(f, `>`, true))
  vm.register("<", (f: var Forth) => forthArith(f, `<`, true))
  vm.register(">=", (f: var Forth) => forthArith(f, `>=`, true))
  vm.register("<=", (f: var Forth) => forthArith(f, `<=`, true))
  vm.register("=", (f: var Forth) => forthArith(f, `==`, true))
  vm.register("and", (f: var Forth) => forthArith(f, `and`, true))
  vm.register("or",  (f: var Forth) => forthArith(f, `or`,  true))
  vm.register(".", showTop)
  vm.register(".s", showStack)
  vm.register("swap", swap)
  vm.register("dup", dup)
  vm.register("rot", rot)
  vm.register("over", over)
  vm.register("cr", (f: var Forth) => echo())
  vm.register("spaces", spaces)
  vm.register("emit", emit)
  vm.register("drop", drop)
  vm.register("mod", (f: var Forth) => forthArith(f, `mod`))
  vm.register("/mod", divmod)
  vm.register("2swap", swapDouble)
  vm.register("2dup", dupDouble)
  vm.register("2over", overDouble)
  vm.register("2drop", dropDouble)
  vm.register("2+", (f: var Forth) => forthArithDouble(f, `+`))
  vm.register("2-", (f: var Forth) => forthArithDouble(f, `-`))
  vm.register("2/", (f: var Forth) => forthArithDouble(f, `div`))
  vm.register("2*", (f: var Forth) => forthArithDouble(f, `*`))
  vm.register("2>", (f: var Forth) =>  forthArithDouble(f,  `>`, true))
  vm.register("2<", (f: var Forth) =>  forthArithDouble(f,  `<`, true))
  vm.register("2>=", (f: var Forth) => forthArithDouble(f, `>=`, true))
  vm.register("2<=", (f: var Forth) => forthArithDouble(f, `<=`, true))
  vm.register("2=", (f: var Forth) =>  forthArithDouble(f, `==`, true))
  vm.register("2.", showTopDouble)
  vm.register("4.", showTopQuad)
  vm.register("4dup", dupQuad)
  vm.register("to-double", toDouble)
  vm.register("2dw", toDouble)
  #vm.register("if", (f: var Forth) => f.constructIfThen(TokenType.`if`))
  #vm.register("then", (f: var Forth) => f.constructIfThen(TokenType.then))
  vm.register("true", (f: var Forth) => (discard f.data.push(-1 as uint16)))
  vm.register("false", (f: var Forth) => (discard f.data.push 0'u16))
  vm.register(">r", toR)
  vm.register("r>", fromR)
  vm.register("I", iR)
  vm.register("r@", iR)
  vm.register("J", jR)

template passWhenCommented(vm: Forth, token: string): untyped =
  if vm.runState[0] == rsComment and not token.endsWith ")":
    continue
template passWhenInString(vm: Forth, token: string): untyped =
  if vm.runState[0] == rsString and not token.endsWith "\"":
    continue

proc eval(vm: var Forth, image: string): RunState =
  result = vm.runState[0]
  var commentToEnd = false
  if vm.runState[0] == rsString:
    let start = 0
    var (inline, strbuf) = image.handleString start
    var count = 1
    strbuf = '\n' & strbuf
    for i, c in strbuf:
      vm.mem.buf[vm.mem.pos+i+1] = byte c
      inc count
    if vm.runState.len > 1 and vm.runState[1] == rsInterpret:
      vm.mem.buf[(vm.data[0].pos) as byte] += byte count
    elif vm.runState.len > 1 and vm.runState[1] == rsCompile:
      vm.mem.buf[(vm.compileConstruct.construct[vm.compileConstruct.construct.len-1].mempos) as byte] += byte count
    inc vm.mem.pos, count
  var start = 0
  for token in image.splitWhitespace:
    if commentToEnd: continue
    if token == "\\":
      commentToEnd = true
      continue

    vm.passWhenCommented token
    vm.passWhenInString token

    if token == "bye": return rsHalt

    if vm.runState[0] == rsComment and token.endsWith ")":
      vm.runState[0] = rsCompile
    elif token == "(" and vm.runState[0] == rsInterpret:
      echo "Cannot handle comment in interpreter"
    elif token == "(" and vm.runState[0] == rsCompile:
      vm.runState[0] = rsComment
    elif vm.runState[0] == rsCompile and vm.compileConstruct.name == "":
      vm.compileConstruct.name = token
    elif token.isNumber:
      let val = token.parseInt
      putData(vm, val, vm.runState[0])
    elif token == ".\"":
      vm.runState.addFirst rsString
      start = image.find(".\"", start) + 2
      let (endInline, stringbuf) = handleString(image, start)
      var count = 0
      for i, c in stringbuf:
        vm.mem.buf[vm.mem.pos+i+1] = byte c
        inc count
      vm.mem.buf[vm.mem.pos] = byte(count)
      let data = Cell(kind: CellType.memory, pos: vm.mem.pos as uint16)
      if vm.runState.len > 1 and vm.runState[1] == rsInterpret:
        discard vm.data.push data
      elif vm.runState.len > 1 and vm.runState[1] == rsCompile:
        vm.compileConstruct.construct.add initTokenObject(data)
      inc vm.mem.pos, count+1

    elif vm.runState[0] == rsString and token.endsWith('\"'):
      if vm.runState.len > 1:
        discard vm.runState.popFirst
      else:
        vm.runState[0] = rsInterpret
    elif token == ":":
      vm.runState[0] = rsCompile
    elif vm.ifthenConstruct("if", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.if)
    elif vm.ifthenConstruct("then", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.then)
    elif vm.ifthenConstruct("loop", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.loop)
    elif vm.ifthenConstruct("else", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.else)
    elif vm.ifthenConstruct("do", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.do)
    elif token == ";" and vm.runState[0] == rsCompile:
      vm.runState[0] = rsInterpret
      dump vm.compileConstruct
      vm.constructDef
      vm.compileConstruct = CompileConstruct()
    elif vm.runState[0] == rsCompile:
      vm.compileConstruct.construct.add initTokenObject(token)
    elif token in vm.dict:
      vm.dict[token](vm)

  if vm.show:
    stdout.write " ok"
    vm.show = false
  result = vm.runState[0]

proc main =
  echo "start forth"
  var vm = Forth(
    data: initStack(),
    ret: initStack(),
    dict: newTable[string, (f: var Forth) -> void](),
    compileConstruct: CompileConstruct(),
    runState: initDeque[RunState](),
  )
  vm.runState.addFirst rsInterpret
  vm.registration
  dump vm.data.sizeof
    
  block repl:
    var line: string
    while true:
      var c = getch()
      if c.ord == 0: continue
      if c == '\n' or c == '\r' or c == '\L':
        stdout.write ' '
        if vm.eval(line) == rsHalt: break
        stdout.write '\n'
        line = ""
      else:
        stdout.write c
        if c == '\b':
          if line.len > 1: line = line[0..^2]
          stdout.write ' '
          stdout.write c
          continue
        line &= c

main()
