theory sample3
  imports Main begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

term "\<lambda>x::vname. 0::val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus xs ys) s = aval xs s + aval ys s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) =  N n" |
  "asimp_const (V x) =  V x" |
  "asimp_const (Plus xs ys) = 
  (case (asimp_const xs, asimp_const ys) of
    (N n, N m) \<Rightarrow> N(n + m) |
    (p, q) \<Rightarrow> Plus p q)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N x) (N y) = N(x + y)" |
  "plus (N x) a = 
    (if x = 0 then
      a
    else
      Plus (N x) a)" |
  "plus a (N x) = 
    (if x = 0 then
      a
    else
      Plus a (N x))" |
  "plus x y = Plus x y"

thm plus.induct

lemma aval_plus [simp]: "aval (plus x y) s = aval x s + aval y s"
  apply (induction x y rule: plus.induct)
  apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus x y) =  plus (asimp x) (asimp y)"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
  apply(auto)
  done

datatype bexp = Bc bool | Not bexp | 
  And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v" |
  "bval (Not b) s = (\<not> bval b s)" |
  "bval (And x y) s = (bval x s \<and> bval y s)" |
  "bval (Less x y) s = (aval x s < aval y s)"

fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True) = Bc False" |
  "not (Bc False) = Bc True" |
  "not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and b (Bc True) = b" |
  "and (Bc False) b = Bc False" |
  "and b (Bc False) = Bc False" |
  "and x y = And x y"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N x) (N y) = Bc (x < y)" |
  "less x y = Less x y"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc value) = Bc value" |
  "bsimp (Not b) = not (bsimp b)" |
  "bsimp (And bx by) = and (bsimp bx) (bsimp by)" |
  "bsimp (Less ax ay) = less (asimp ax) (asimp ay)"

lemma "bval (bsimp b) s = bval b s"
  sorry




