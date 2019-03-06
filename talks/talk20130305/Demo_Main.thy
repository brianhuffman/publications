theory Demo_Main
imports
  Complex_Main
  "~~/src/HOL/Library/Multiset"
begin

hide_const (open) Int.intrel Groups.plus Multiset.mult

hide_type (open) Int.int

definition mrel :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<approx>" 50)
  where "xs \<approx> ys \<longleftrightarrow> multiset_of xs = multiset_of ys"

lemma mrel_refl [simp]: "xs \<approx> xs"
  unfolding mrel_def by simp

definition union_mset :: "'a multiset multiset \<Rightarrow> 'a multiset"
(*
  where "union_mset = Multiset.fold (op +) {#}"
*)
  where "union_mset = fold_mset (op +) {#}"


notation fun_rel (infixr "===>" 55)

end
