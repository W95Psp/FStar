module Test

open FStar.Tactics

let _ = 
  assert (True) by (
    let se = lookup_typ (top_env ()) ["Prims";"PURE"] in
    ( match se with
    | Some x -> fail "some"
    | None -> fail "none"
    );
    // let _ = inspect_sigelt se in
    fail "ok"
  )

// let _ = `%PURE

