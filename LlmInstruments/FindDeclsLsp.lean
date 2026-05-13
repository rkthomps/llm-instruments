
import Lean


namespace LlmInstruments

open Lean
open Lean.Lsp

structure FindDeclsParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson
