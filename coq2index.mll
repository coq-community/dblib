{

(* The purpose of this script is to read all .glob files and build a
   global index. To a name [x], this index should be able to associate
   a set of modules that refer to [x]. (A set of modules is a coarse
   piece of information; one could be more precise, but it is not
   clear whether this is worth the trouble.) The index is dumped as
   an HTML file. *)

(* At each definition of a name [x], [coq2html] produces a link to the
   index entry for [x]. On the other hand, [coq2index] produces an
   index entry for [x] only if there exists at least one reference
   to [x] -- either within the same unit or within some other unit.
   So the system is not quite perfect. *)

open Printf

(* ------------------------------------------------------------------------- *)

(* Building the index. *)

module StringSet =
  Set.Make(String)

type source =
  string

type sources =
  StringSet.t

type target =
  string * string (* unit, path *)
  (* one could use triples of the form unit/path/namespace, but the namespaces
     used by Coq do not seem to be consistent, e.g. a definition may use "prf"
     as a namespace while references to the definition use "prfax" *)

let index : (target, sources) Hashtbl.t =
  Hashtbl.create 273

let path sp id =
  match sp, id with
  | "<>", "<>" -> ""
  | "<>", _    -> id
  | _   , "<>" -> sp
  | _   , _    -> sp ^ "." ^ id

let is_local_module dp =
  Sys.file_exists (dp ^ ".v")

let add_reference curmod dp sp id =
  if is_local_module dp then (* filter out references to other libraries *)
    let path = path sp id in
    if path <> "" then (* filter out references to nothing (the module itself?) *)
      let source : source = curmod in
      let target : target = (dp, path) in
      let sources : StringSet.t =
	try
	  Hashtbl.find index target
	with Not_found ->
	  StringSet.empty
      in
      if not (StringSet.mem source sources) then
	Hashtbl.replace index target (StringSet.add source sources)

let add_definition curmod sp id =
  let path = path sp id in
  assert (path <> "");
  let target : target = (curmod, path) in
  if not (Hashtbl.mem index target) then
    Hashtbl.add index target StringSet.empty
    (* ensures that every definition gets an index entry, even if there is no
       reference to it *)

(* ------------------------------------------------------------------------- *)

(* Dumping the index in text form. *)

let dump () =
  Hashtbl.iter (fun (unit, path) sources ->
    printf "%s %s" unit path;
    StringSet.iter (fun source ->
      printf " %s" source
    ) sources;
    printf "\n"
  ) index;
  flush stdout

(* ------------------------------------------------------------------------- *)

(* Converting the index to curried [unit -> path -> sources] form. *)

module StringMap =
  Map.Make(String)

let extend_map (unit_data : 'a) (extend_data : 'a -> 'b -> 'a) (m : 'a StringMap.t) (key : string) (new_data : 'b) =
  let existing_data : 'a =
    try
      StringMap.find key m
    with Not_found ->
      unit_data
  in
  StringMap.add key (extend_data existing_data new_data) m

type cindex =
  StringSet.t StringMap.t StringMap.t

let extend_cindex : cindex -> string -> string * StringSet.t -> cindex =
  extend_map StringMap.empty (fun m (path, sources) -> StringMap.add path sources m)

let currify () : cindex =
  Hashtbl.fold (fun (unit, path) sources cindex ->
    extend_cindex cindex unit (path, sources)
  ) index StringMap.empty

(* ------------------------------------------------------------------------- *)

(* Dumping the index in HTML form. *)

let start_html_page () =
  printf "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">

<head>
<meta http-equiv=\"Content-Type\" content=\"text/html; charset=iso-8859-1\" />
<title>Index</title>
<meta name=\"description\" content=\"Index\" />
<link href=\"coq2index.css\" rel=\"stylesheet\" type=\"text/css\" />
</head>
"

let end_html_page () =
  printf "\
</body>
</html>
"

let html (cindex : cindex) =
  start_html_page();
  (* Beginning of index. *)
  StringMap.iter (fun unit path_sources ->
    (* Beginning of a unit. *)
    printf "<h1>%s</h1>\n" unit;
    (* List all references to this unit. *)
    StringMap.iter (fun path sources ->
      (* Beginning of a path. *)
      printf "<div class=\"entry\">\n";
      printf "<span class=\"path\">\n  <a name=\"%s.%s\">%s</a>\n</span>\n" unit path path;
      printf "<span class=\"sources\">\n";
      (* List all sources of references to this path. *)
      if StringSet.is_empty sources then
	printf "No references.\n"
      else begin
	let sources = StringSet.remove unit sources in
	if StringSet.is_empty sources then
	  printf "No external references.\n"
	else
	  StringSet.iter (fun source ->
	    printf "  <a href=\"%s.html\">%s</a>.\n" source source
	  ) sources
      end;
      (* End of sources list. *)
      printf "</span>\n</div>\n"
    ) path_sources;
    (* End of unit. *)
    printf "\n<br/>\n"
  ) cindex;
  (* End of index. *)
  end_html_page();
  flush stdout

(* ------------------------------------------------------------------------- *)

(* Parsing .glob files. *)

let current_module = ref None

exception Globfile

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let xref = ['A'-'Z' 'a'-'z' '0'-'9' '_' '.']+ | "<>"
let integer = ['0'-'9']+

rule globfile = parse
  | eof
      { () }
  | "F" (ident as m) space* "\n"
      { current_module := Some m;
        globfile lexbuf }
  | "R" integer
    space+ (xref as dp)
    space+ (xref as sp)
    space+ (xref as id)
    space+ ident
    space* "\n"
      { match !current_module with
        | Some curmod ->
	    add_reference curmod dp sp id;
	    globfile lexbuf
	| None ->
	    raise Globfile }
  | ident
    space+ integer
    space+ (xref as sp)
    space+ (xref as id)
    space* "\n"
      { match !current_module with
        | Some curmod ->
	    add_definition curmod sp id;
	    globfile lexbuf
	| None ->
	    raise Globfile }
  | [^ '\n']* "\n"
      { globfile lexbuf }
  | _
      { raise Globfile }

(* ------------------------------------------------------------------------- *)

(* Processing the command line. *)

{

let process_file f =
  if Filename.check_suffix f ".glob" then begin
    current_module := None;
    let ic = open_in f in
    begin try
      globfile (Lexing.from_channel ic)
    with Globfile ->
      fprintf stderr "coq2index: warning: file \"%s\" appears ill-formed.\n%!" f
    end;
    close_in ic
  end else begin
    eprintf "Don't know what to do with file %s\n" f;
    exit 2
  end

let () =
  Arg.parse [] process_file "Usage: coq2index <file.glob> ... <file.glob>\n";
  html(currify())

}
