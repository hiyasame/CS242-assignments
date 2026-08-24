open Core
open Option.Monad_infix

exception Unimplemented

(* Set this to true to print out intermediate state between Karel steps *)
let debug = false

type cell =
  | Empty
  | Wall
  | Beeper

type grid = cell list list

type dir =
  | North
  | West
  | South
  | East

type pos = int * int

type state = {
  karel_pos : pos;
  karel_dir : dir;
  grid : grid;
}

let get_cell (grid : grid) ((i, j) : pos) : cell option =
  (List.nth grid j) >>= fun l -> List.nth l i
;;

let set_cell (grid : grid) ((i, j) : pos) (cell : cell) : grid =
  List.mapi grid ~f:(fun j' l ->
    if j = j' then List.mapi l ~f:(fun i' c -> if i = i' then cell else c)
    else l)
;;

let state_to_string (state : state) : string =
  let str_grid = List.mapi state.grid ~f:(fun y list ->
    List.mapi list ~f:(fun x cell ->
      let (kx, ky) = state.karel_pos in
        if kx = x && ky = y then
          "K"
        else match cell with
          | Empty -> "."
          | Wall -> "x"
          | Beeper -> "B")) in
    String.concat ~sep:"\n" (List.map str_grid ~f:(String.concat ~sep:" "))
;;

let empty_grid (m : int) (n : int) : grid =
  List.map (List.range 0 m) ~f:(fun _ ->
    List.map (List.range 0 n) ~f:(fun _ -> Empty))
;;

type predicate =
  | FrontIs of cell
  | NoBeepersPresent
  | Facing of dir
  | Not of predicate

type instruction =
  | Move
  | TurnLeft
  | PickBeeper
  | PutBeeper
  | While of predicate * instruction list
  | If of predicate * instruction list * instruction list

let rec predicate_to_string (pred : predicate) : string =
  match pred with
  | FrontIs c ->
    let cellstr = match c with
      | Empty -> "Empty" | Beeper -> "Beeper" | Wall -> "Wall"
    in
    Printf.sprintf "FrontIs(%s)" cellstr
  | NoBeepersPresent -> "NoBeepersPresent"
  | Facing dir ->
    let dirstr = match dir with
      | North -> "North" | South -> "South" | East -> "East" | West -> "West"
    in
    Printf.sprintf "Facing(%s)" dirstr
  | Not pred' -> Printf.sprintf "Not(%s)" (predicate_to_string pred')

let rec instruction_to_string (instr : instruction) : string =
  match instr with
  | Move -> "Move"
  | TurnLeft -> "TurnLeft"
  | PickBeeper -> "PickBeeper"
  | PutBeeper -> "PutBeeper"
  | While (pred, instrs) ->
    Printf.sprintf "While(%s, [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string instrs)
  | If (pred, then_, else_) ->
    Printf.sprintf "If(%s, [%s], [%s])"
      (predicate_to_string pred)
      (instruction_list_to_string then_)
      (instruction_list_to_string else_)
and instruction_list_to_string (instrs: instruction list) : string =
  String.concat ~sep:", " (List.map ~f:instruction_to_string instrs)


let rec eval_pred (state : state) (pred : predicate) : bool =
  match pred with
    | FrontIs cell -> let (x, y) = state.karel_pos in
      let actual_cell_opt = match state.karel_dir with
        | North -> get_cell state.grid (x, y-1)
        | South -> get_cell state.grid (x, y+1)
        | East -> get_cell state.grid (x+1, y)
        | West -> get_cell state.grid (x-1, y) in
          (match actual_cell_opt with
            | Some actual_cell -> Poly.(actual_cell = cell)
            | None -> Poly.(cell = Wall))
    | NoBeepersPresent -> let (x, y) = state.karel_pos in
      Poly.(get_cell state.grid (x, y) <> Some Beeper)
    | Facing dir -> Poly.(dir = state.karel_dir)
    | Not p -> not (eval_pred state p)


let rec step (state : state) (code : instruction) : state =
  match code with
  | Move ->
      if eval_pred state (FrontIs Wall) then
        state
      else
        let (x, y) = state.karel_pos in
        let new_pos : pos =
          match state.karel_dir with
          | North -> (x, y - 1)
          | South -> (x, y + 1)
          | East -> (x + 1, y)
          | West -> (x - 1, y)
        in
        { state with karel_pos = new_pos }
  | TurnLeft ->
      let new_dir : dir =
        match state.karel_dir with
        | North -> West
        | West -> South
        | South -> East
        | East -> North
      in
      { state with karel_dir = new_dir }
  | PickBeeper ->
      if eval_pred state NoBeepersPresent then
        state
      else
        { state with grid = set_cell state.grid state.karel_pos Empty }
  | PutBeeper ->
      if eval_pred state NoBeepersPresent then
        { state with grid = set_cell state.grid state.karel_pos Beeper }
      else
        state
  | While (pred, instrs) ->
      if eval_pred state pred then
        let state' = step_list state instrs in
        step state' (While (pred, instrs))
      else
        state
  | If (pred, then_, else_) ->
      if eval_pred state pred then
        step_list state then_
      else
        step_list state else_

and step_list (state : state) (instrs : instruction list) : state =
  List.fold instrs ~init:state ~f:(fun state instr ->
    if debug then
       (Printf.printf "Executing instruction %s...\n"
          (instruction_to_string instr);
        let state' = step state instr in
        Printf.printf "Executed instruction %s. New state:\n%s\n"
          (instruction_to_string instr)
          (state_to_string state');
        state')
     else
       step state instr)

;;

let checkers_algo : instruction list =
  let advance : instruction =
    If (NoBeepersPresent, [Move; PutBeeper], [Move])
  in
  let fill_row : instruction =
    While (Not (FrontIs Wall), [advance])
  in
  let descend_and_face_west : instruction =
    If (
      FrontIs Wall,
      [],
      [advance; TurnLeft; TurnLeft; TurnLeft]
    )
  in
  let descend_and_face_east : instruction =
    If (FrontIs Wall, [], [advance; TurnLeft])
  in
  [
    PutBeeper;
    While (
      Not (Facing South),
      [
        fill_row;
        If (
          Facing East,
          [TurnLeft; TurnLeft; TurnLeft; descend_and_face_west],
          [TurnLeft; descend_and_face_east]
        );
      ]
    );
  ]
