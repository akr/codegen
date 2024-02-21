val fix_snippet : string -> string
val add_snippet : string -> unit
val add_header_snippet : string -> unit
val command_snippet : string -> unit
val command_header_snippet : string -> unit
val command_rawsnippet : string -> unit
val command_header_rawsnippet : string -> unit
val add_thunk : (unit -> string) -> unit
val add_header_thunk : (unit -> string) -> unit
