theory sample4
  imports Main begin

(* inductive one of evenness *)
inductive ev  :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
(*evSS: "ev n \<Longrightarrow> ev (n + 2)*)
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc(n)))"

(*
  How do we prove that some number is even,
  e.g., ev 4? Simply by combining the 
  defining rules for ev:
  ev 0 =\<Rightarrow> ev (0 + 2) =\<Rightarrow> ev((0 + 2) + 2) = ev 4
*)

(* recursive one of evenness *)
fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True" |
  "evn (Suc 0) = False" |
  "evn (Suc (Suc n)) = evn n"

lemma "ev(Suc(Suc(Suc(Suc 0::nat))))"
  apply(rule evSS)
  apply(rule evSS)
  apply(rule ev0)
  done

lemma agree_ev_evn [simp]: "ev m \<Longrightarrow> evn m"
  apply(induction rule: ev.induct)
(*
  apply(simp)
  apply(simp)
*)
  apply(simp_all)
  done

(*declare ev.intros[simp, intro]*)

lemma "evn n \<Longrightarrow> ev n"
  apply(induction n rule: evn.induct)
    apply(simp_all add: ev0 evSS)
  done
  

  
  