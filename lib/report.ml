type term_entry =
  { term : Pp.document;
    value : Pp.document
  }
[@@deriving yojson]

type predicate_clause_entry =
  { cond : Pp.document;
    clause : Pp.document
  }
[@@deriving yojson]

type resource_entry =
  { res : Pp.document;
    res_span : Pp.document
  }

type where_report =
  { fnction : string option;
    section : string option;
    loc_cartesian : ((int * int) * (int * int)) option;
    loc_head : string (* loc_pos: string; *)
  }
[@@deriving yojson]

(* Different forms of a document. *)
type simp_view =
  { original : Pp.document; (* original view *)
    simplified : Pp.document list (* simplified based on model *)
  }
[@@deriving yojson]

type label = string

let lab_interesting : label = "interesting"

let lab_uninteresting : label = "uninteresting"

let lab_invalid = "Resources that do not satisfy predicate definitions"

let lab_unknown = "Resources that may not satisfy predicate definitions"

let lab_valid = "Resources that do satisfy predicate definitions"

let sequence (xs : ('a, 'e) Result.t list) : ('a list, 'e) Result.t =
  let ( let* ) = Result.bind in
  let rcons e es =
    let* v = e in
    let* vs = es in
    Ok (v :: vs)
  in
  List.fold_right rcons xs (Ok [])


module StrMap = struct
  module M = Map.Make (String)

  let to_yojson (value_to_yojson : 'v -> Yojson.Safe.t) (map : 'v M.t) : Yojson.Safe.t =
    `Assoc (List.map_snd value_to_yojson (M.bindings map))


  let of_yojson
        (value_of_yojson : Yojson.Safe.t -> ('v, string) Result.t)
        (json : Yojson.Safe.t)
    : ('v M.t, string) Result.t
    =
    match json with
    | `Assoc elems ->
      let ( let* ) = Result.bind in
      let elems' =
        List.map
          (fun (key, json_value) ->
             let* value = value_of_yojson json_value in
             Ok (key, value))
          elems
      in
      let* bindings = sequence elems' in
      Ok (M.of_seq (List.to_seq bindings))
    | _ -> Error ("StrMap.of_yojson: expected `Assoc, found " ^ Yojson.Safe.to_string json)


  include M
end

(* Things classified in various ways.
   To start we just have "interesting" and "uninteresting", but we could add more *)
type 'a labeled_view = 'a list StrMap.t [@@deriving yojson]

let labeled_empty = StrMap.empty

let add_labeled lab view mp = StrMap.add lab view mp

let get_labeled mp lab = StrMap.find_opt lab mp

type state_report =
  { where : where_report;
    invalid_resources : simp_view labeled_view;
    not_given_to_solver : simp_view labeled_view;
    resources : simp_view labeled_view;
    constraints : simp_view labeled_view;
    terms : term_entry labeled_view
  }
[@@deriving yojson]

type report =
  { trace : state_report list;
    requested : Pp.document option;
    unproven : Pp.document (* * Pp.document *) option;
    predicate_hints : predicate_clause_entry list
  }
[@@deriving yojson]

let list elements = String.concat "" elements

let enclose tag what = "<" ^ tag ^ ">" ^ what ^ "</" ^ tag ^ ">"

(* let html elements = enclose "html" (list elements) *)
(* let head = enclose "head" *)
(* let style = enclose "style" *)
let _link ~url ~text = "<a href=\"" ^ url ^ "\">" ^ text ^ "</a>"

let div ?clss ?id elements =
  let clss = match clss with Some clss -> " class=\"" ^ clss ^ "\"" | None -> "" in
  let id = match id with Some id -> " id=\"" ^ id ^ "\"" | None -> "" in
  let opent = "<div" ^ clss ^ id ^ ">" in
  let closet = "</div>" in
  opent ^ list elements ^ closet


(* let pre code = enclose "pre" code *)
(* let body elements = enclose "body" (list elements) *)
let h i title body = list [ enclose ("h" ^ string_of_int i) title; body ]

let table_row cols = enclose "tr" (list (List.map (enclose "td") cols))

let table_head_row cols = enclose "tr" (list (List.map (enclose "th") cols))

let table_head cols = enclose "thead" (table_head_row cols)

let table_body rows = enclose "tbody" (list (List.map table_row rows))

let table head rows = enclose "table" (list [ table_head head; table_body rows ])

let table_without_head rows = enclose "table" (list [ table_body rows ])

let details summary more = enclose "details" (list [ enclose "summary" summary; more ])

let oguard o f = match o with None -> "" | Some x -> f x

let lguard l f = match l with [] -> "" | _ -> f l

(* let make_requested requested =  *)
(*   oguard requested (fun re -> *)
(*     h 1 "Requested resource" ( *)
(*       table ["requested"; "byte span"] *)
(*         [[Pp.plain re.res; Pp.plain re.res_span]] *)
(*     ) *)
(*   ) *)

let cartesian_to_string = function
  | None -> ""
  | Some ((start_line, start_col), (end_line, end_col)) ->
    Printf.sprintf "%d:%d-%d:%d" start_line start_col end_line end_col


let make_where where =
  let or_empty = function Some s -> s | None -> "" in
  table
    [ "function"; "section"; "location" ]
    [ [ div ~clss:"loc_function" [ or_empty where.fnction ];
        div ~clss:"loc_section" [ or_empty where.section ];
        div ~clss:"loc" [ cartesian_to_string where.loc_cartesian ]
        (* pre (where.loc_pos) *)
      ]
    ]


let make_requested requested =
  oguard requested (fun re ->
    h
      1
      "Requested resource"
      (table_without_head (* ["requested"; (\* "byte span" *\)] *)
         [ [ Pp.plain re (* Pp.plain re.res_span *) ] ]))


let make_unproven unproven =
  oguard unproven (fun c ->
    h
      1
      "Unproven constraint (simplified)"
      (table_without_head (* ["constraint"; "simplified constraint"] *)
         [ [ Pp.plain c (* Pp.plain (snd c) *) ] ]))


let make_predicate_hints predicate_hints =
  lguard predicate_hints (fun predicate_hints ->
    h
      1
      "Possibly relevant predicate clauses"
      (table
         [ "condition"; "clause" ]
         (List.map
            (fun pce -> [ Pp.plain pce.cond; Pp.plain pce.clause ])
            predicate_hints)))


(* let make_resources resources =  *)
(*   h 1 "Available resources" ( *)
(*     match resources with *)
(*     | [] -> "(no available resources)" *)
(*     | _ -> *)
(*       table ["resource"; "byte span and match"] *)
(*         (List.map (fun re -> [Pp.plain re.res; Pp.plain re.res_span]) resources) *)
(*   ) *)

let interesting_uninteresting mk_table render data =
  let get_data lab =
    match StrMap.find_opt lab data with
    | None -> ("", true)
    | Some xs -> (mk_table (List.map render xs), List.is_empty xs)
  in
  let interesting_table, no_interesting = get_data lab_interesting in
  let uninteresting_table, no_uninteresting = get_data lab_uninteresting in
  match (no_interesting, no_uninteresting) with
  | true, true -> "(none)"
  | _, true -> interesting_table
  | true, _ -> details "more" uninteresting_table
  | _, _ -> interesting_table ^ details "more" uninteresting_table


let simp_view s =
  let btn = div ~clss:"toggle" [] in
  let val_orig = Pp.plain s.original in
  let val_simp = Pp.plain (Pp.separate Pp.hardline s.simplified) in
  if String.equal val_orig val_simp then
    [ val_orig ]
  else
    [ div [ btn; div [ val_simp ]; div [ val_orig ] ] ]


let table_by_label mk_table render data main_lab labs =
  let get_table lab =
    match StrMap.find_opt lab data with
    | None -> (lab, "(none)")
    | Some t -> (lab, mk_table (List.map render t))
  in
  let tables = List.map get_table labs in
  let combine_tables acc (new_lab, new_table) = acc ^ details new_lab new_table in
  List.fold_left combine_tables (snd (get_table main_lab)) tables


let make_invalid_resources rs =
  let rs' = StrMap.filter (fun _ v -> not (List.is_empty v)) rs in
  if StrMap.is_empty rs' then
    ""
  else
    h
      1
      lab_invalid
      (table_by_label
         table_without_head
         simp_view
         rs'
         lab_invalid
         [] (* Issue #900: [ lab_unknown; lab_valid ] *))


let make_not_given_to_solver ds =
  h
    1
    "Definitions and constraints not handled automatically"
    (interesting_uninteresting table_without_head simp_view ds)


let make_resources rs =
  h 1 "Available resources" (interesting_uninteresting table_without_head simp_view rs)


let make_terms ts =
  let render v = [ Pp.plain v.term; Pp.plain v.value ] in
  h 1 "Terms" (interesting_uninteresting (table [ "term"; "value" ]) render ts)


let make_constraints cs =
  h 1 "Constraints" (interesting_uninteresting table_without_head simp_view cs)


let css =
  {|
html {
  font-family: sans-serif;
  font-size: 11pt
}

body {
  padding: 0;
  margin: 0;
  overflow: hidden;
}

table {
  width: 100%;
  border: 1px solid;
  border-collapse: collapse;
}

h1 {
  font-size: 11pt;
  margin-top: 16pt;
}

tr {
  padding: 0;
  margin: 0;
}

.hidden {
  display: none;
}

th, td {
  text-align: left;
  vertical-align: top;
  border-left: 1px solid;
  border-right: 1px solid;
  padding-left: 5px;
  padding-right: 5px;
  padding-top: 3px;
  padding-bottom: 3px;
  white-space: pre;
}

th {
  padding-top: 5px;
  padding-bottom: 5px;
}

th {
  font-weight: normal;
  font-style: italic;
}

#root {
  display: flex;
  height: 100vh;
  margin: 0;
  padding: 0;
}

.menu {
  font-size: 15px;
  margin: 0px;
  padding: 0px;
  vertical-align: middle;
}

.menu ul {
  list-style-type: none;
  display: inline;
  padding: 0;
  margin: 0;
}

.menu li {
  padding: 0px;
  margin: 0px;
  float: left;
}

.menu button {
  all: unset;
  padding: 7px;
}

.toggle {
  border-radius: 2px;
  display: inline-block;
  font-size: small;
  cursor: pointer;
}

#pageinfo {
  padding: 7px;
  display: inline-block;
}

#sectioninfo {
  padding: 7px;
  display: inline-block;
}

#cn_state {
  width: 50%;
  align-content: flex-start;
  display: grid;
}

#pages {
  padding: 10px;
  overflow-y:scroll;
}

#cn_code_display {
  width: 50%;
  display: grid;
  align-content: flex-start;
}

#cn_code {
  overflow-y:scroll;
  /* padding: 5px; */
  font-family: monospace;
  white-space-collapse: preserve;
  /* text-wrap: nowrap; */
  white-space: pre;
}

.nb {
  padding-left: 5px;
  /* TODO this will clip if there are more than 999 lines */
  width: 35px;
}

.hl {
    display: inline;
}

.line {
  padding-left: 8px;
  /* overflow:scroll; */
}

@media (prefers-color-scheme: dark) {

  html {
    background-color: black;
    color: lightgray;
  }

  table, th, td {
    border-color: #303030;
  }

  tr {
    background-color: #181818;
  }

  tr:nth-child(even) {
    background-color: #222222;
  }

  th {
    background-color: #252525;
    border-bottom: 1px solid #303030;
  }

  tr:hover {
    background-color: #101044;
  }

  .hl {
    background-color: #2727a6;
  }

  .menu {
    background-color: #CCCCCC;
    color: black;
  }

  .menu button:hover {
    background-color: #AAAAAA;
  }

  #cn_code {
    background-color: rgb(30, 30, 30);
  }

  .nb {
    width: 35px;
    color: rgb(150, 150, 150);
    background-color: rgb(50, 50, 50);
  }

  .toggle {
    background-color: #CCCCCC;
    color: black;
  }
}

@media (prefers-color-scheme: light) {

  html {
    background-color: white;
    color: black;
  }

  table, th, td {
    border-color: #E9E9E9;
  }

  tr {
    background-color: #F8F8F8;
  }

  th {
    background-color: #F0F0F0;
    border-bottom: 1px solid #E9E9E9;
  }

  tr:hover {
    background-color: #E2F0FF;
  }

  .hl {
    background-color: #b4d8fd;
  }

  .menu {
    background-color: #333333;
    color: white;
  }

  .menu button:hover {
    background-color: #555555;
  }

  #cn_code {
    background-color: rgb(245, 245, 245);
  }

  .nb {
    width: 35px;
    color: rgb(150, 150, 150);
    background-color: rgb(230, 230, 230);
  }

  .toggle {
    background-color: #333333;
    color: white;
  }
}
|}


let script =
  {|
var current_page = 1
const menu = document.getElementById("menu1").getElementsByTagName("li")
const pageinfo = document.getElementById("pageinfo")
const pages = document.getElementById("pages").children
const cn_code = document.getElementById("cn_code")
const n_pages = pages.length


function clear_highlight() {
  Array.from(document.getElementById("cn_code").children).forEach((e) => {
    div = e.children[1]
    div.replaceChildren(div.textContent)
  })
}

function highlight(line, start_col, end_col) {
  // console.log(`HIGHLIGHT(${line}, ${start_col}, ${end_col})`)
  if (end_col <= start_col) {
    end_col = start_col+1
  }
  Array.from(cn_code.children).forEach((e, n) => {
    div = e.children[1]
    if (n != line-1) {
      div.replaceChildren(div.textContent)
    } else {
      str = div.textContent
      before = str.substring(0, start_col-1)
      hl = document.createElement("span")
      hl.classList.add("hl")
      hl.textContent = str.substring(start_col-1,end_col-1)
      after = str.substring(end_col-1)
      div.replaceChildren(before,hl,after)
      cn_code.scrollTop = div.offsetTop
    }
  })
}

function multiline_highlight(start_line, start_col, end_line, end_col) {
  Array.from(cn_code.children).forEach((e, n) => {
    div = e.children[1]
    if (n < start_line || end_line < n) {
      div.replaceChildren(div.textContent)
    } else {
      str = div.textContent
      if (n == start_line) {
        cn_code.scrollTop = div.offsetTop
      }
      hl = document.createElement("span")
      hl.classList.add("hl")
      // TODO: probably could be written nicer
      if (start_line == end_line) {
        before = str.substring(0, start_col)
        hl.textContent = str.substring(start_col,end_col)
        after = str.substring(end_col)
        div.replaceChildren(before,hl,after)
      } else if (n == start_line) {
        before = str.substring(0, start_col)
        hl.textContent = str.substring(start_col)
        div.replaceChildren(before,hl)
      } else if (n == end_line) {
        hl.textContent = str.substring(0,end_col)
        after = str.substring(end_col)
        div.replaceChildren(hl,after)
      } else {
        hl.textContent = str
        div.replaceChildren(hl)
      }
    }
  })
}

// function decode_loc(n) {
//   loc = pages[n-1].getElementsByClassName("loc")[0].textContent
//   console.log("DECODING ==> ", loc)
//   if (loc == "") {
//     // console.log("NO LOC")
//     clear_highlight()
//   } else {
//     xs = loc.split(" ")[1].split(":")
//     line = xs[1]
//     col = parseInt(xs[2])
//     // console.log(`LOC ==> line: ${line} -- col: ${col}`)
//     highlight(line, col, col+1)
//   }
// }

function decode_loc(n) {
  loc = pages[n-1].getElementsByClassName("loc")[0].textContent
  fnction = pages[n-1].getElementsByClassName("loc_function")[0].textContent
  section = pages[n-1].getElementsByClassName("loc_section")[0].textContent
  if (loc == "") {
    clear_highlight()
  } else {
    pair = loc.split("-")
    start = pair[0].split(":")
    end = pair[1].split(":")
    multiline_highlight(start[0], start[1], end[0], end[1])
  }
  if (fnction == "") {
    sectioninfo.textContent = "(none)"
  }
  else if (section == "") {
    sectioninfo.textContent = fnction
  }
  else {
    sectioninfo.textContent = `${fnction}  >  ${section}`
  }
}

function goto_page(n) {
  if (0 < n && n <= n_pages ) {
    // console.log(`GOTO_PAGE(${n} ==> current: ${current_page})`)
    decode_loc(n)
    pages[current_page - 1].style.display = "none"
    pages[n-1].style.display = "block"
    current_page = n

    pageinfo.textContent = `[${current_page} / ${n_pages}]`
    menu[0].disabled = false
    menu[1].disabled = false
    menu[2].disabled = false
    menu[3].disabled = false
    if (current_page == 1) {
      menu[0].disabled = true
      menu[1].disabled = true
    } else if (current_page == n_pages) {
      menu[2].disabled = true
      menu[3].disabled = true
    }
  }
}

function goto_prev() {
  goto_page(current_page-1)
}

function goto_next() {
  goto_page(current_page+1)
}

function create_line(n, str) {
  nb_div = document.createElement("div")
  str_div = document.createElement("div")
  nb_div.textContent = n
  nb_div.classList.add("nb")
  str_div.textContent = str
  str_div.classList.add("line")
  ret = document.createElement("div")
  ret.style.display = "flex"
  ret.replaceChildren(nb_div, str_div)
  return ret
}

function make_toggles(className, labels) {
  for(const btn of document.getElementsByClassName(className)) {
    const opts = []
    for (let i = btn.nextSibling; i !== null; i = i.nextSibling) {
      i.classList.add("hidden")
      opts.push(i)
    }
    console.log(opts)
    let cur = 0
    function update() {
      cur %= opts.length
      const lab = labels && labels[cur] || ("Option " + (cur + 1))
      btn.textContent = lab
      opts[cur].classList.remove("hidden")
    }
    btn.addEventListener("click", () => {
      opts[cur].classList.add("hidden")
      ++cur
      update()
    })
    update()
  }
}

function init() {
  make_toggles("toggle",["Simplified","Original"])
  lines = cn_code.textContent.split("\n")
  lines.forEach((e, n) => {
    if (n == 0) {
      cn_code.replaceChildren(create_line(1, e))
    } else {
      cn_code.appendChild(create_line(n+1, e))
    }
  })

  goto_page(1)

  Array.from(pages).forEach((e, i) => {
    if (i != 0) {
      e.style.display = "none"
    }
  })
}

init()
|}


let make_state (report : state_report) requested unproven predicate_hints =
  div
    ~clss:"page"
    [ div ~clss:"hidden" [ make_where report.where ];
      make_requested requested;
      make_unproven unproven;
      make_predicate_hints predicate_hints;
      make_invalid_resources report.invalid_resources;
      make_not_given_to_solver report.not_given_to_solver;
      make_resources report.resources;
      make_terms report.terms;
      make_constraints report.constraints
    ]


let mk_html ~title ~pages ~file_content ~n_pages =
  {|
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>|}
  ^ title
  ^ {|</title>
<style>|}
  ^ css
  ^ {|</style>
</head>

<div id="root">
  <div id="cn_state">
  <div class="menu" id="menu1">
    <ul>
    <li><button onclick="goto_page(1)"/>first</button></li>
    <li><button onclick="goto_prev()"/>prev</button></li>
    <li><button onclick="goto_next()"/>next</button></li>
    <li><button onclick="goto_page(|}
  ^ string_of_int n_pages
  ^ {|)"/>last</button></li>
    </ul>
    <div id="pageinfo"></div>
  </div>
  |}
  ^ pages
  ^ {|
  </div>
<div id="cn_code_display">
<div class="menu" id="menu2">
  <div id="sectioninfo"></div>
</div>
|}
  ^ file_content
  ^ {|
</div>
</div>

<script defer>|}
  ^ script
  ^ {|</script>
</html>
|}


let read_file filename =
  try
    let ic = open_in filename in
    Some (In_channel.input_all ic)
  with
  | _ -> None


let make filename source_filename_opt (report : report) =
  let n_pages = List.length report.trace in
  assert (n_pages > 0);
  let _menu =
    div
      ~id:"menu"
      [ {|<input type="button" value="first" onclick="goto_page(|}
        ^ string_of_int 1
        ^ {|)"/>|};
        {|<input type="button" value="prev" onclick="goto_prev()"/>|};
        {|<input type="button" value="next" onclick="goto_next()"/>|};
        {|<input type="button" value="last" onclick="goto_page(|}
        ^ string_of_int n_pages
        ^ {|)"/>|}
      ]
  in
  let pages =
    div
      ~id:"pages"
      (List.map
         (fun state ->
            make_state state report.requested report.unproven report.predicate_hints)
         report.trace)
  in
  let file_content =
    match Option.bind source_filename_opt read_file with
    | None -> "NO FILE CONTENT FOUND"
    | Some str -> str
  in
  let oc = open_out filename in
  output_string
    oc
    (mk_html
       ~title:"CN state explorer"
       ~pages
       ~file_content:(div ~id:"cn_code" [ file_content ])
       ~n_pages);
  close_out oc;
  filename
