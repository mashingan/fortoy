import tables, strutils, deques
from sugar import `=>`, `->`, dump
from terminal import getch

type
  #Stack = Deque[uint16]
  Stack = object
    data: array[1024, Cell]
    pos: Natural
  EvalState = object
    show: bool
    getAddress: bool
  Forth = object
    data: Stack
    ret: Stack
    dict: TableRef[string, uint16]
    address: seq[(f: var Forth) -> void]
    mem: Memory
    state: EvalState
    compileConstruct: CompileConstruct
    runState: Deque[RunState]

  Word = uint16
  DoubleWord = array[2, Word]

  Memory = object
    pos: Natural
    buf: array[1024, byte]

  CellType {.size: 1, pure.} = enum
    data memory address

  Cell {.packed.} = object
    case kind: CellType
    of CellType.data:
      data: uint16
    of CellType.memory:
      pos: uint16
    of CellType.address:
      address: uint16

  StackError = object of CatchableError
  ConstructError = object of CatchableError

  RunState {.size:1} = enum
    rsInterpret rsCompile rsComment rsHalt rsString

  TokenType {.size:1, pure.} = enum
    data word `if` `else` then noop loop `do` `string` `break`

  TokenObject = object
    case kind: TokenType
    of TokenType.data:
      data: Cell
    of TokenType.word:
      word: string
    of TokenType.string:
      mempos: uint16
    of TokenType.if, TokenType.else, TokenType.then, TokenType.noop,
      TokenType.do, TokenType.loop, TokenType.break:
      discard

  CompileConstruct = object
    name: string
    construct: seq[TokenObject]

proc sizeof(st: Stack): Natural =
  result = st.data.sizeof + st.pos.sizeof

proc sizeof(m: Memory): Natural =
  result = m.buf.sizeof + m.pos.sizeof

proc sizeof(cc: CompileConstruct): Natural =
  result = cc.name.sizeof + cc.construct.sizeof

proc sizeof(vm: Forth): Natural =
  result = vm.data.sizeof + vm.ret.sizeof + vm.dict.sizeof +
    vm.mem.sizeof + vm.state.sizeof + vm.compileConstruct.sizeof +
    vm.address.sizeof + vm.runState.sizeof

converter toU16(c: Cell): uint16 =
  if c.kind == CellType.data:
    result = c.data

converter toCell(u: uint16): Cell =
  result = Cell(kind: CellType.data, data: u)

template `as`(a, b: untyped): untyped =
  cast[`b`](`a`)

proc initTokenObject(kind: TokenType): TokenObject =
  const spectypes ={ TokenType.if, TokenType.then, TokenType.loop,
    TokenType.else, TokenType.do, TokenType.break}
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
    result = (Cell(), StackError(name: "StackError", msg: move e.msg))

proc push[T: Cell|uint16](stack: var Stack, value: T): (bool, StackError) =
  stack.addFirst value
  result = (true, StackError())

proc register(f: var Forth, word: string, prc: proc(f: var Forth)) =
  let curr = f.address.len
  f.dict[word] = curr.uint16
  f.address.add prc

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

template isNumber(token: string, op: untyped, t: typedesc): untyped =
  try:
    let val = `t`(`op`(token))
    result = (true, val)
  except:
    var init: t
    result = (false, init)

proc isInt(token: string): (bool, int) =
  isNumber(token, parseInt, int)

proc isFloat(token: string): (bool, float32) =
  isNumber(token, parseFloat, float32)

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
  of CellType.address:
    stdout.write("address:", v.address.uint16, ' ')
  f.state.show = true

proc showTopDouble(f: var Forth) =
  let (p1, err1) = f.data.pop
  handleErr err1
  let (p2, err2) = f.data.pop
  handleErr err2
  let p = [p1.toU16, p2.toU16] as uint32
  stdout.write(p as int32, ' ')
  f.state.show = true

proc showTopQuad(f: var Forth) =
  var data: array[4, uint16]
  for i in 0 .. 3:
    let (someval, err) = f.data.pop
    data[i] = someval.toU16
    handleErr err
  let p = data as uint64

  stdout.write(p as int64,' ')
  f.state.show = true

proc showTopFloat(f: var Forth) =
  checkBinary f
  let (f1, err1) = f.data.pop
  handleErr err1
  let (f2, err2) = f.data.pop
  handleErr err2
  let flo32 = [f1.toU16, f2.toU16] as float32
  stdout.write flo32, ' '
  f.state.show = true

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
      of CellType.address:
        stdout.write("address:", cell.address, ' ')
    stdout.write "] "
  f.state.show = true

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
  f.state.show = true

proc emit(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  stdout.write chr(v.toU16)
  f.state.show = true

proc drop(f: var Forth) =
  let (_, err) = f.data.pop
  handleErr err

template forthArithFloat(f: var Forth, op: untyped, booleanop = false): untyped =
  checkArity f, 4
  retrieveBinaryDouble f
  let p1 = [p11.toU16, p12.toU16] as float32
  let p2 = [p21.toU16, p22.toU16] as float32
  let val = `op`(p2, p1 )
  if booleanop:
    discard f.data.push(if bool(val): -1 as uint16 else: 0)
  else:
    let data = (val as float32) as DoubleWord
    for i in countdown(data.high, 0):
      discard f.data.push data[i]

proc constructBody(f: var Forth, cc: CompileConstruct): ConstructError =
  # dump cc
  var isTrue = true
  var idx = 0
  var lastjumpIdx = initDeque[int]()
  var lastLoopCount = initDeque[int16]()
  var nextjumpIdx = initDeque[int]()
  for i, obj in cc.construct:
    case obj.kind
    of TokenType.do:
      lastjumpIdx.addLast i
    of TokenType.loop:
      nextjumpIdx.addFirst i
    else:
      discard
  if lastjumpIdx.len != nextjumpIdx.len:
    return ConstructError(msg: "Invalid construct do-loop pair")
  while idx <= cc.construct.high:
    let obj = cc.construct[idx]
    if obj.kind == TokenType.then:
      inc idx
      isTrue = true
      continue
    elif obj.kind == TokenType.else:
      isTrue = not isTrue
      inc idx
      continue
    if not isTrue:
      inc idx
      continue

    case obj.kind
    of TokenType.data:
      discard f.data.push obj.data
    of TokenType.string:
      discard f.data.push(Cell(kind: CellType.memory, pos: obj.mempos))
    of TokenType.word:
      if f.dict.hasKey(obj.word):
        if f.state.getAddress:
          discard f.data.push Cell(kind: CellType.address, address: f.dict[obj.word])
          f.state.getAddress = false
        else:
          f.address[f.dict[obj.word]](f)
    of TokenType.if:
      let (testTrue, err) = f.data.pop
      handleErr err
      let trueTrue = testTrue.toU16 as int16
      isTrue = trueTrue == -1
    of TokenType.do:
      let (looping, err) = f.data.pop
      handleErr err
      let loopTime = looping.toU16 as int16
      lastLoopCount.addFirst loopTime
      discard f.ret.push 0'u16
    of TokenType.loop:
      if lastjumpIdx.len > 0 and lastLoopCount.len > 0:
        var count = lastLoopCount.popFirst
        if count > 1:
          for i, dopos in nextjumpIdx:
            if idx == dopos:
              idx = lastjumpIdx[i]
              break
          dec count
          lastLoopCount.addFirst count
          let (c, err) = f.ret.pop
          handleErr err
          if c.kind == CellType.data:
            discard f.ret.push(c.toU16 + 1)
        else:
          discard f.ret.pop
    of TokenType.break:
      for i, nextjmp in nextjumpIdx:
        if nextjmp > idx:
          idx = nextjmp
          break
      discard f.ret.pop
      
    of TokenType.noop, TokenType.else, TokenType.then:
      discard

    inc idx
  return ConstructError()

proc constructDef(vm: var Forth) =
  var cc = vm.compileConstruct
  var closure = proc(f: var Forth) =
    var err = f.constructBody cc
    if err.msg != "": echo err.msg

  vm.register(vm.compileConstruct.name, move closure)

proc putData(vm: var Forth, val: int|float32, runState: RunState) =
  template addTo(n: static[int], isCompiled: static[bool], typ: typedesc) =
    let data = (val as typ) as array[n, uint16]
    for i in countdown(data.high, 0):
      when isCompiled:
        vm.compileConstruct.construct.add initTokenObject(data[i])
      else:
        discard vm.data.push data[i]

  when val.type is int:
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
  elif val.type is float32:
    if runState == rsCompile:
      addTo(2, true, float32)
    else:
      addTo(2, false, float32)

proc toDouble(f: var Forth) =
  let (v, err) = f.data.pop
  handleErr err
  let vv = (v.toU16) as int16 as int32 as uint32 as DoubleWord
  for i in countdown(vv.high, 0):
    discard f.data.push vv[i]

proc toFloat(f: var Forth) =
  checkBinary f
  retrieveBinary f
  let f32 = ([v1.toU16, v2.toU16] as uint32).int32.float32
  let vv = f32 as DoubleWord
  for i in countdown(vv.high, 0):
    discard f.data.push vv[i]

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
  vm.register("dswap", swapDouble)
  vm.register("ddup", dupDouble)
  vm.register("dover", overDouble)
  vm.register("ddrop", dropDouble)
  vm.register("d+", (f: var Forth) => forthArithDouble(f, `+`))
  vm.register("d-", (f: var Forth) => forthArithDouble(f, `-`))
  vm.register("d/", (f: var Forth) => forthArithDouble(f, `div`))
  vm.register("d*", (f: var Forth) => forthArithDouble(f, `*`))
  vm.register("d>", (f: var Forth) =>  forthArithDouble(f,  `>`, true))
  vm.register("d<", (f: var Forth) =>  forthArithDouble(f,  `<`, true))
  vm.register("d>=", (f: var Forth) => forthArithDouble(f, `>=`, true))
  vm.register("d<=", (f: var Forth) => forthArithDouble(f, `<=`, true))
  vm.register("d=", (f: var Forth) =>  forthArithDouble(f, `==`, true))
  vm.register("d.", showTopDouble)
  vm.register("q.", showTopQuad)
  vm.register("qdup", dupQuad)
  vm.register("to-double", toDouble)
  vm.register("2dw", toDouble)
  vm.register("f.", showTopFloat)
  vm.register("f+", (f: var Forth) =>  forthArithFloat(f, `+`))
  vm.register("f-", (f: var Forth) =>  forthArithFloat(f, `-`))
  vm.register("f*", (f: var Forth) =>  forthArithFloat(f, `*`))
  vm.register("f/", (f: var Forth) =>  forthArithFloat(f, `/`))
  vm.register("f>", (f: var Forth) =>  forthArithDouble(f,  `>`, true))
  vm.register("f<", (f: var Forth) =>  forthArithDouble(f,  `<`, true))
  vm.register("f>=", (f: var Forth) => forthArithDouble(f, `>=`, true))
  vm.register("f<=", (f: var Forth) => forthArithDouble(f, `<=`, true))
  vm.register("f=", (f: var Forth) =>  forthArithDouble(f, `==`, true))
  vm.register("to-float", toFloat)
  vm.register("d2float", toFloat)
  vm.register("w2float", (f: var Forth) => (f.toDouble; f.toFloat))
  vm.register("true", (f: var Forth) => (discard f.data.push(-1 as uint16)))
  vm.register("false", (f: var Forth) => (discard f.data.push 0'u16))
  vm.register(">r", toR)
  vm.register("r>", fromR)
  vm.register("I", iR)
  vm.register("r@", iR)
  vm.register("J", jR)
  vm.register("@", (f: var Forth) => (f.state.getAddress = true))
  vm.register("!", proc(f: var Forth) =
    let (data, err) = f.data.pop
    handleErr err
    if data.kind != CellType.address: return
    f.address[data.address](f))
  vm.register("bye", (f: var Forth) => (f.runState[0] = rsHalt))

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
    var (_, strbuf) = image.handleString start
    var count = 1
    strbuf = '\n' & strbuf
    for i, c in strbuf:
      vm.mem.buf[vm.mem.pos+i+1] = byte c
      inc count
    if vm.runState.len > 1 and vm.runState[1] == rsInterpret:
      vm.mem.buf[(vm.data[0].pos) as byte] += byte count
    elif vm.runState.len > 1 and vm.runState[1] == rsCompile:
      vm.mem.buf[(vm.compileConstruct.construct[
        vm.compileConstruct.construct.len-1].mempos) as byte] += byte count
    inc vm.mem.pos, count
  var start = 0
  for token in image.splitWhitespace:
    if vm.runState[0] == rsHalt: return rsHalt
    if commentToEnd: continue
    if token == "\\":
      commentToEnd = true
      continue

    vm.passWhenCommented token
    vm.passWhenInString token

    if vm.runState[0] == rsComment and token.endsWith ")":
      vm.runState[0] = rsCompile
    elif token == "(" and vm.runState[0] == rsInterpret:
      echo "Cannot handle comment in interpreter"
    elif token == "(" and vm.runState[0] == rsCompile:
      vm.runState[0] = rsComment
    elif vm.runState[0] == rsCompile and vm.compileConstruct.name == "":
      vm.compileConstruct.name = token
    elif token == ".\"":
      vm.runState.addFirst rsString
      start = image.find(".\"", start) + 2
      let (_, stringbuf) = handleString(image, start)
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
    elif vm.ifthenConstruct("break", token):
      vm.compileConstruct.construct.add initTokenObject(TokenType.break)
    elif token == ";" and vm.runState[0] == rsCompile:
      vm.runState[0] = rsInterpret
      # dump vm.compileConstruct
      vm.constructDef
      vm.compileConstruct = CompileConstruct()
    elif token in vm.dict and vm.runState[0] == rsInterpret:
      if vm.state.getAddress:
        let data = Cell(kind: CellType.address, address: vm.dict[token])
        discard vm.data.push data
        vm.state.getAddress = false
      else:
        vm.address[vm.dict[token]](vm)
    elif (var (isnum, val) = token.isInt; isnum):
      putData(vm, val, vm.runState[0])
    elif (var (isnum, val) = token.isFloat; isnum and token != "."):
      putData(vm, val, vm.runState[0])
    elif vm.runState[0] == rsCompile:
      if vm.state.getAddress:
        let data = Cell(kind: CellType.address, address: vm.dict[token])
        vm.compileConstruct.construct.add initTokenObject(data)
        vm.state.getAddress = false
      else:
        vm.compileConstruct.construct.add initTokenObject(token)

  if vm.state.show:
    stdout.write " ok"
    vm.state.show = false
  result = vm.runState[0]

when isMainModule:
  proc main =
    echo "start forth"
    var vm = Forth(
      data: initStack(),
      ret: initStack(),
      dict: newTable[string, uint16](),
      address: newSeqOfCap[(f: var Forth) -> void](1024),
      compileConstruct: CompileConstruct(),
      runState: initDeque[RunState](),
    )
    vm.runState.addFirst rsInterpret
    vm.registration
    #dump vm.data.sizeof
    dump vm.sizeof
    for k, v in vm.fieldPairs:
      dump k.sizeof
      dump v.sizeof
    
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
            if line.len > 0: line = line[0..^2]
            stdout.write ' '
            stdout.write c
            continue
          line &= c

  main()
