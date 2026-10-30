/-
  LeanSys.JsonRpc: Zero-Copy JSON-RPC 2.0 Envelope Framing & Dispatcher over `JsonTape`
  (`0 import Lean`, `0 sorryAx`)
  - Parses JSON-RPC 2.0 requests (`{"jsonrpc":"2.0","id":...,"method":"...","params":...}`)
    directly from a borrowed `ByteSlice` using `LeanSys.Codec.JsonTape`
  - Every frame is gated by `LeanSys.Spec.verifyJsonRpcFrame` (`leansys_verify_jsonrpc_frame`)
  - Formats canonical JSON-RPC 2.0 success and error responses for MCP stdio servers (`workspace-mcp`, `control-mcp`)
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Codec

namespace LeanSys.JsonRpc

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Codec

/-- Parsed zero-copy JSON-RPC 2.0 request frame. -/
structure RpcRequest where
  idRaw?     : Option String
  method     : String
  paramsTape : Option JsonTape
  rawTape    : JsonTape

/-- Standard JSON-RPC 2.0 error codes. -/
@[inline] def errParseError     : Int := -32700
@[inline] def errInvalidRequest : Int := -32600
@[inline] def errMethodNotFound : Int := -32601
@[inline] def errInvalidParams  : Int := -32602
@[inline] def errInternalError  : Int := -32603

/--
  Parse and validate a JSON-RPC 2.0 request frame from `line : ByteSlice`,
  gated by `leansys_verify_jsonrpc_frame`.
-/
def parseRequest? (line : ByteSlice) : Option RpcRequest := do
  let tape := JsonTape.indexJsonObject line
  let ver ← JsonTape.lookupString? tape "jsonrpc"
  let hasV2 : UInt8 := if ver == "2.0" then 1 else 0
  let method ← JsonTape.lookupString? tape "method"
  let idSlice? := JsonTape.lookupSlice? tape "id"
  let hasId : UInt8 := if idSlice?.isSome then 1 else 0
  if verifyJsonRpcFrame hasV2 hasId method.utf8ByteSize.toUInt32 line.len.toUInt64 != 1 then
    none
  else
    let idRaw? := match JsonTape.findEntry? tape "id" with
      | none => none
      | some e =>
        let s : ByteSlice := { ba := tape.root.ba, off := e.valOff, len := e.valLen }
        some (if e.isString then s!"\"{s.toStringLossy}\"" else s.toStringLossy)
    let paramsTape := (JsonTape.lookupSlice? tape "params").map (fun (ps, _) => JsonTape.indexJsonObject ps)
    some { idRaw? := idRaw?, method := method, paramsTape := paramsTape, rawTape := tape }

/-- Render a JSON-RPC 2.0 success response line. -/
def formatSuccess (idRaw? : Option String) (resultJson : String) : String :=
  let idField := idRaw?.getD "null"
  s!"\{\"jsonrpc\":\"2.0\",\"id\":{idField},\"result\":{resultJson}}"

/-- Render a JSON-RPC 2.0 error response line. -/
def formatError (idRaw? : Option String) (code : Int) (message : String) : String :=
  let idField := idRaw?.getD "null"
  s!"\{\"jsonrpc\":\"2.0\",\"id\":{idField},\"error\":\{\"code\":{code},\"message\":\"{message}\"}}"


/-- Zero-copy JSON-RPC 2.0 request frame indexed directly over a `ByteSource` (`BorrowedSlice` or `ByteSlice`). -/
structure BorrowedRpcRequest where
  idRaw?     : Option String
  method     : String
  paramsTape : Option BorrowedJsonTape
  rawTape    : BorrowedJsonTape

/-- Parse and validate a JSON-RPC 2.0 request directly from a `ByteSource` (`mmap` / `io_uring` / `&[u8]`)
    without copying the wire frame, gated by `leansys_verify_jsonrpc_frame`. -/
def parseRequestSource? (src : ByteSource) : Option BorrowedRpcRequest := do
  let tape := BorrowedJsonTape.indexSource src
  let ver ← BorrowedJsonTape.lookupString? tape "jsonrpc"
  let hasV2 : UInt8 := if ver == "2.0" then 1 else 0
  let method ← BorrowedJsonTape.lookupString? tape "method"
  let idEntry? := BorrowedJsonTape.findEntry? tape "id"
  let hasId : UInt8 := if idEntry?.isSome then 1 else 0
  if verifyJsonRpcFrame hasV2 hasId method.utf8ByteSize.toUInt32 src.size.toUInt64 != 1 then
    none
  else
    let idRaw? := match idEntry? with
      | none => none
      | some e =>
        match tape.root.subSource? e.valOff e.valLen with
        | none => none
        | some s => some (if e.isString then s!"\"{s.toStringLossy}\"" else s.toStringLossy)
    let paramsTape := (BorrowedJsonTape.lookupSource? tape "params").map fun (ps, _) => BorrowedJsonTape.indexSource ps
    some { idRaw? := idRaw?, method := method, paramsTape := paramsTape, rawTape := tape }

@[inline]
def parseRequestBorrowed? (v : BorrowedSlice) : Option BorrowedRpcRequest :=
  parseRequestSource? (ByteSource.ofBorrowed v)

end LeanSys.JsonRpc
