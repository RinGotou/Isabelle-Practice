theory sample5
  imports Main begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

thm star.induct

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  (* apply(simp add:refl) *)
  (* for subgoal 1. The first one is P x x,
   the result of case refl*)
   apply(assumption)
  apply(metis step)
  done
