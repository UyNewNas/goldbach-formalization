      decimalNumberFn startPos includeWhitespace c (s.next c startPos)
    else
      s.mkError "numeral"

def isIdCont : ParserContext → ParserState → Bool := fun c s =>
  let i    := s.pos
  let curr := c.get i
  if curr == '.' then
    let i := c.next i
    if c.atEnd i then
      false
    else
      let curr := c.get i
      isIdFirst curr || isIdBeginEscape curr
  else
    false

private def isToken (idStartPos idStopPos : String.Pos.Raw) (tk : Option Token) : Bool :=
  match tk with
  | none    => false
  | some tk =>
     -- if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
    tk.utf8ByteSize ≥ idStartPos.byteDistance idStopPos


def mkTokenAndFixPos (startPos : String.Pos.Raw) (tk : Option Token) : ParserFn := fun c s =>
  match tk with
  | none    => s.mkErrorAt "token" startPos
  | some tk =>
    if c.forbiddenTk? == some tk then
      s.mkErrorAt "forbidden token" startPos
    else
      let leading   := c.mkEmptySubstringAt startPos
      let stopPos   := startPos + tk
      let s         := s.setPos stopPos
      let s         := whitespace c s
      let wsStopPos := s.pos
      let trailing  := c.substring (startPos := stopPos) (stopPos := wsStopPos)
      let atom      := mkAtom (SourceInfo.original leading startPos trailing stopPos) tk
      s.pushSyntax atom

def mkIdResult (startPos : String.Pos.Raw) (tk : Option Token) (val : Name)
    (includeWhitespace : Bool := true) :
    ParserFn := fun c s =>
  let stopPos           := s.pos
  if isToken startPos stopPos tk then
    mkTokenAndFixPos startPos tk c s
  else
    let rawVal          := c.substring startPos stopPos
    let s               := if includeWhitespace then whitespace c s else s
    let trailingStopPos := s.pos
    let leading         := c.mkEmptySubstringAt startPos
    let trailing        := c.substring (startPos := stopPos) (stopPos := trailingStopPos)
    let info            := SourceInfo.original leading startPos trailing stopPos
    let atom            := mkIdent info rawVal val
    s.pushSyntax atom

partial def identFnAux (startPos : String.Pos.Raw) (tk : Option Token) (r : Name)
    (includeWhitespace : Bool := true) :
    ParserFn :=
  let rec parse (r : Name) (c s) :=
    let i := s.pos
    if h : c.atEnd i then
      s.mkEOIError
    else
      let curr := c.get' i h
      if isIdBeginEscape curr then
        let startPart := c.next' i h
        let s         := takeUntilFn isIdEndEscape c (s.setPos startPart)
        if h : c.atEnd s.pos then
          s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
        else
          let stopPart  := s.pos
          let s         := s.next' c s.pos h
          let r := .str r (c.extract startPart stopPart)
          if isIdCont c s then
            let s := s.next c s.pos
            parse r c s
          else
            mkIdResult startPos tk r includeWhitespace c s
      else if isIdFirst curr then
        let startPart := i
        let s         := takeWhileFn isIdRest c (s.next c i)
        let stopPart  := s.pos
        let r := .str r (c.extract startPart stopPart)
        if isIdCont c s then
          let s := s.next c s.pos
          parse r c s
        else
          mkIdResult startPos tk r includeWhitespace c s
      else
        mkTokenAndFixPos startPos tk c s
  parse r

private def isIdFirstOrBeginEscape (c : Char) : Bool :=
  isIdFirst c || isIdBeginEscape c

private def nameLitAux (startPos : String.Pos.Raw) : ParserFn := fun c s =>
  let s := identFnAux startPos none .anonymous (includeWhitespace := true) c (s.next c startPos)
  if s.hasError then
    s
