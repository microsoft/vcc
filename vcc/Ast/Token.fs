namespace Microsoft.Research.Vcc

[<AbstractClass>]
type public Token() =
  
  let mutable related : Token option = None

  abstract Line : int with get
  abstract Column : int with get
  abstract Byte : int with get
  abstract Filename : string with get
  abstract Value : string with get

  abstract member SuppressWarning : int->bool
  default this.SuppressWarning _ = false

  member this.Related
    with get() = related
    and set(value) = related <- value

  static member NoToken = DummyToken.Instance

and public DummyToken() =
  inherit Token()

  static member private instance = new DummyToken() :> Token

  override this.Line = 0
  override this.Column = 0
  override this.Byte = 0
  override this.Filename = "<no file>"
  override this.Value = System.String.Empty

  static member Instance with get() = DummyToken.instance

and public LazyToken(getToken : unit -> Token) =
  inherit Token()

  let token = lazy getToken()

  static member Create(getToken : System.Func<Token>) = 
    let f() = getToken.Invoke()
    LazyToken(f : unit -> Token)

  override this.Line = token.Value.Line
  override this.Column = token.Value.Column
  override this.Byte = token.Value.Byte
  override this.Filename = token.Value.Filename
  override this.Value = token.Value.Value
  override this.SuppressWarning(code) = token.Value.SuppressWarning(code)

  member this.DelayedToken with get() = token.Value

and public ForwardingToken(tok : Token, related, getValue) as this =
  inherit Token()

  do this.Related <- related

  override this.Line = tok.Line
  override this.Column = tok.Column
  override this.Byte = tok.Byte
  override this.Filename = tok.Filename
  override this.Value = getValue()

  member this.WrappedToken with get() = tok

  new(tok, getValue) = ForwardingToken(tok, None, getValue)

and WarningSuppressingToken(tok, warning) =
  inherit ForwardingToken(tok, None, fun () -> tok.Value)

  override this.SuppressWarning code = code = warning || base.SuppressWarning(code)