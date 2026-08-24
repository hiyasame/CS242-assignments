open Core

exception Unimplemented

type ngram = string list
type ngram_map = (ngram, string list) Map.Poly.t
type word_distribution = float String.Map.t

let rec remove_last_impl1 (l : string list) : string list =
  (
    match l with
    | [] | [_] -> []
    | h :: t -> h :: (remove_last_impl1 t)
  )
;;

assert (Poly.(remove_last_impl1 ["a"; "b"] = ["a"]));
;;

let remove_last_impl2 (l : string list) : string list =
  List.filteri l ~f:(fun (i : int)(_ : string) : bool ->
    i <> List.length l - 1)
;;

assert (Poly.(remove_last_impl2 ["a"; "b"] = ["a"]))
;;

let compute_ngrams (words : string list) (n : int) : string list list =
  let (acc, cur) =
    List.fold_left words ~init:([], [])
      ~f:(fun ((acc : string list list), (cur : string list)) (word : string) ->
        if List.length cur < n then
          (acc, cur @ [ word ])
        else
          (acc @ [ cur ], (List.drop cur 1) @ [ word ]))
  in
  acc @ [ cur ]
;;

assert (Poly.(compute_ngrams ["a"; "b"; "c"] 2 = [["a"; "b"]; ["b"; "c"]]));
;;

let ngram_to_string ng =
  Printf.sprintf "[%s]" (String.concat ~sep:", " ng)
;;

let ngram_map_new () : ngram_map =
  Map.Poly.empty
;;

let ngram_map_add (map : ngram_map) (ngram : ngram) : ngram_map =
  let (prefix, suffix) =
    List.split_n ngram (List.length ngram - 1)
  in
  match suffix with
  | [word] ->
      let previous_words : string list =
        match Map.Poly.find map prefix with
        | None -> []
        | Some words -> words
      in
      Map.Poly.set map
        ~key:prefix
        ~data:(previous_words @ [word])
  | _ -> map
;;

let () =
  let map = ngram_map_new () in
  let map = ngram_map_add map ["a"; "b"] in
  assert (Poly.(Map.Poly.find map ["a"] = Some ["b"]));

  let map = ngram_map_add map ["a"; "c"] in
  assert (Poly.(Map.Poly.find map ["a"] = Some ["b"; "c"]));

  let map = ngram_map_add map ["x"; "y"] in
  assert (Poly.(Map.Poly.find map ["a"] = Some ["b"; "c"]));
  assert (Poly.(Map.Poly.find map ["x"] = Some ["y"]));
  assert (Poly.(Map.Poly.find map ["missing"] = None));

  let map = ngram_map_new () in
  let map = ngram_map_add map ["a"; "b"; "c"] in
  assert (Poly.(Map.Poly.find map ["a"; "b"] = Some ["c"]));
  ()
;;

let ngram_map_distribution (map : ngram_map) (ngram : ngram)
  : word_distribution option =
  match Map.Poly.find map ngram with
  | None -> None
  | Some words ->
      let total : float =
        float_of_int (List.length words)
      in
      let counts : word_distribution =
        List.map words ~f:(fun (word : string) ->
          (word, 1.))
        |> String.Map.of_alist_reduce ~f:(+.)
      in
      Some (
        String.Map.map counts ~f:(fun (count : float) ->
          count /. total)
      )
;;

let distribution_to_string (dist : word_distribution) : string =
  Sexp.to_string_hum (String.Map.sexp_of_t Float.sexp_of_t dist)
;;

let sample_distribution (dist : word_distribution) : string =
  let random_value : float = Random.float 1. in

  let (result, _) =
    Map.fold dist
      ~init:(None, 0.)
      ~f:(fun
        ~(key: string)
        ~(data: float)
        ((selected, cumulative) : string option * float) ->
          match selected with
          | Some _ -> (selected, cumulative)
          | None ->
            let next_cumulative = cumulative +. data in
            if Float.compare random_value next_cumulative < 0 then
              (Some key, next_cumulative)
            else
              (None, next_cumulative))
  in

  match result with
  | Some word -> word
  | None -> failwith "invalid or empty distribution"
;;

let rec sample_n (map : ngram_map) (ng : ngram) (n : int) : string list =
  if n <= 0 then
    []
  else
    match ngram_map_distribution map ng with
    | None ->
        []
    | Some distribution ->
        let word : string =
          sample_distribution distribution
        in
        let next_ng : ngram =
          List.drop (ng @ [word]) 1
        in
        word :: sample_n map next_ng (n - 1)
;;
