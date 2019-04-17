type 'a state =
  | Partial of 'a partial
  | Done    of int * 'a
  | Fail    of int * string list * string
and 'a partial =
  { committed : int
  ; continue  : Bigstringaf.t -> off:int -> len:int -> More.t -> 'a state }

type 'a with_state = Input.t ->  int -> More.t -> 'a

type 'a failure = (string list -> string -> 'a state) with_state
type ('a, 'r) success = ('a -> 'r state) with_state

type ('a, 'r) a =
  { input : Input.t
  ; pos : int
  ; more : More.t
  ; succ : ('a, 'r) success
  ; fail : 'r failure }

type 'a t =
  (* Input.t -> int -> More.t
     ->
     (Input.t -> int -> More.t -> (string list -> string -> 'r state))
     ->
     (Input.t -> int -> More.t -> 'a -> 'r state)
     ->
     'r state *)
  { run : 'r. ('a, 'r) a -> 'r state } [@@unbox]

let fail_k    input pos _ marks msg = Fail(pos - Input.client_committed_bytes input, marks, msg)
let succeed_k input pos _       v   = Done(pos - Input.client_committed_bytes input, v)

let fail_to_string marks err =
  String.concat " > " marks ^ ": " ^ err

let state_to_option = function
  | Done(_, v) -> Some v
  | _          -> None

let state_to_result = function
  | Done(_, v)          -> Ok v
  | Partial _           -> Error "incomplete input"
  | Fail(_, marks, err) -> Error (fail_to_string marks err)

let parse p =
  let input = Input.create Bigstringaf.empty ~committed_bytes:0 ~off:0 ~len:0 in
  p.run { input; pos= 0; more= Incomplete; fail= fail_k; succ= succeed_k; }

let parse_bigstring p input =
  let input = Input.create input ~committed_bytes:0 ~off:0 ~len:(Bigstringaf.length input) in
  state_to_result (p.run { input; pos= 0; more= Complete; fail= fail_k; succ= succeed_k; })

module Monad = struct
  let return v =
    { run = fun { input; pos; more; succ; _ } ->
      succ input pos more v
    }

  let fail msg =
    { run = fun { input; pos; more; fail; _ } ->
      fail input pos more [] msg
    }

  let (>>=) p f =
    { run = fun ({ fail; succ; _ } as a) ->
      let succ' input' pos' more' v = (f v).run { input= input'; pos= pos'; more= more'; fail; succ; } in
      p.run { a with succ= succ'; }
    }

  let (>>|) p f =
    { run = fun ({ succ; _ } as a) ->
      let succ' input' pos' more' v = succ input' pos' more' (f v) in
      p.run { a with succ= succ' }
    }

  let (<$>) f m =
    m >>| f

  let (<*>) f m =
    (* f >>= fun f -> m >>| f *)
    { run = fun ({ succ; fail; _ } as a) ->
      let succ0 input0 pos0 more0 f =
        let succ1 input1 pos1 more1 m = succ input1 pos1 more1 (f m) in
        m.run { input= input0; pos= pos0; more= more0; fail; succ= succ1; }
      in
      f.run { a with succ= succ0 } }

  let lift f m =
    f <$> m

  let lift2 f m1 m2 =
    { run = fun ({ fail; succ; _ } as a) ->
      let succ1 input1 pos1 more1 m1 =
        let succ2 input2 pos2 more2 m2 = succ input2 pos2 more2 (f m1 m2) in
        m2.run { input= input1; pos= pos1; more= more1; fail; succ= succ2; }
      in
      m1.run { a with succ= succ1 } }

  let lift3 f m1 m2 m3 =
    { run = fun ({ fail; succ; _ } as a) ->
      let succ1 input1 pos1 more1 m1 =
        let succ2 input2 pos2 more2 m2 =
          let succ3 input3 pos3 more3 m3 =
            succ input3 pos3 more3 (f m1 m2 m3) in
          m3.run { input= input2; pos= pos2; more= more2; fail; succ= succ3; } in
        m2.run { input= input1; pos= pos1; more= more1; fail; succ= succ2; }
      in
      m1.run { a with succ= succ1 } }

  let lift4 f m1 m2 m3 m4 =
    { run = fun ({ fail; succ; _ } as a) ->
      let succ1 input1 pos1 more1 m1 =
        let succ2 input2 pos2 more2 m2 =
          let succ3 input3 pos3 more3 m3 =
            let succ4 input4 pos4 more4 m4 =
              succ input4 pos4 more4 (f m1 m2 m3 m4) in
            m4.run { input= input3; pos= pos3; more= more3; fail; succ= succ4; } in
          m3.run { input= input2; pos= pos2; more= more2; fail; succ= succ3; } in
        m2.run { input= input1; pos= pos1; more= more1; fail; succ= succ2; }
      in
      m1.run { a with succ= succ1 } }

  let ( *>) a b =
    (* a >>= fun _ -> b *)
    { run = fun ({ fail; succ; _ } as x) ->
      let succ' input' pos' more' _ = b.run { input= input'; pos= pos'; more= more'; fail; succ; } in
      a.run { x with succ= succ' }
    }

  let (<* ) a b =
    (* a >>= fun x -> b >>| fun _ -> x *)
    { run = fun ({ fail; succ; _ } as x) ->
      let succ0 input0 pos0 more0 x =
        let succ1 input1 pos1 more1 _ = succ input1 pos1 more1 x in
        b.run { input= input0; pos= pos0; more= more0; fail; succ= succ1; }
      in
      a.run { x with succ= succ0 } }
end

module Choice = struct
  let (<?>) p mark =
    { run = fun ({ fail; _ } as a) ->
      let fail' input' pos' more' marks msg =
        fail input' pos' more' (mark::marks) msg in
      p.run { a with fail= fail' }
    }

  let (<|>) p q =
    { run = fun ({ fail; succ; pos; more; _ } as a) ->
      let fail' input' pos' more' marks msg =
        (* The only two constructors that introduce new failure continuations are
         * [<?>] and [<|>]. If the initial input position is less than the length
         * of the committed input, then calling the failure continuation will
         * have the effect of unwinding all choices and collecting marks along
         * the way. *)
        if pos < Input.parser_committed_bytes input' then
          fail input' pos' more marks msg
        else
          q.run { input= input'; pos; more= more'; fail; succ; } in
      p.run { a with fail= fail' }
    }
end

module Monad_use_for_debugging = struct
  let return = Monad.return
  let fail   = Monad.fail
  let (>>=)  = Monad.(>>=)

  let (>>|) m f = m >>= fun x -> return (f x)

  let (<$>) f m = m >>| f
  let (<*>) f m = f >>= fun f -> m >>| f

  let lift  = (>>|)
  let lift2 f m1 m2       = f <$> m1 <*> m2
  let lift3 f m1 m2 m3    = f <$> m1 <*> m2 <*> m3
  let lift4 f m1 m2 m3 m4 = f <$> m1 <*> m2 <*> m3 <*> m4

  let ( *>) a b = a >>= fun _ -> b
  let (<* ) a b = a >>= fun x -> b >>| fun _ -> x
end
