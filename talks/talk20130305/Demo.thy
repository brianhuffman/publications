theory Demo imports Demo_Main begin

section {* 1. Ordinary Quotient *}

fun intrel :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where "intrel (x, y) (u, v) = (x + v = u + y)"

quotient_type int = "nat \<times> nat" / intrel
  by (intro equivpI reflpI sympI transpI) auto

fun raw_plus :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat"
  where "raw_plus (x, y) (u, v) = (x + u, y + v)"

fun raw_le :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  where "raw_le (x, y) (u, v) = (x + v \<le> u + y)"

lift_definition plus :: "int \<Rightarrow> int \<Rightarrow> int" is raw_plus
  by auto

lift_definition le :: "int \<Rightarrow> int \<Rightarrow> bool" is raw_le
  by auto

lift_definition two :: "int" is "(2, 0)"
  by auto

lift_definition two' :: "int" is "(4, 2)"
  by auto

lemma "two = two'"
apply transfer
apply auto
done

lemma "\<forall>x y. plus x y = plus y x"
  apply transfer
  apply auto
  done

lemma "\<forall>x y z. le x y \<longrightarrow> le (plus x z) (plus y z)"
  apply transfer
  apply auto
  done










section {* 2. Typedef as Quotient *}

typedef (open) posrat = "{x::rat. 0 < x}"
  by (auto intro!: zero_less_one)

setup_lifting type_definition_posrat

lift_definition mult :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "op *"
  by (rule mult_pos_pos)

lift_definition add :: "posrat \<Rightarrow> posrat \<Rightarrow> posrat" is "op +"
  by (rule add_pos_pos)

lift_definition one :: "posrat" is "1"
  by (rule zero_less_one)

lift_definition recip :: "posrat \<Rightarrow> posrat" is "inverse"
  by (rule positive_imp_inverse_positive)

lemma "\<forall>x. mult x (recip x) = one"
  apply transfer
  apply simp
  done








section {* 3. Transfer between pre-existing types *}

definition LM :: "'a list \<Rightarrow> 'a multiset \<Rightarrow> bool"
  where "LM xs X = (multiset_of xs = X)"

lemma [transfer_rule]:
  "(LM ===> LM ===> op =) (op \<approx>) (op =)"
  "(LM ===> LM ===> LM) append (op +)"
  "(LM ===> op =) length size"
  "((op = ===> op =) ===> LM ===> LM) map image_mset"
(*"((LM ===> op =) ===> op =) All All"*)
  "bi_total LM"
  sorry

lemma "\<forall>xs ys::'a multiset. size (xs + ys) = size xs + size ys"
  apply transfer
  apply simp
  done

lemma "\<forall>f g xs. (image_mset f \<circ> image_mset g) xs = image_mset (f \<circ> g) xs"
  apply transfer
  apply simp
  done
(* "op \<circ>" transfers to "op \<circ>", according to this rule: *)
thm comp_transfer





section {* 4. Transfer with nested types *}

definition LM' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b multiset \<Rightarrow> bool"
  where "LM' A = list_all2 A OO LM"

lemma [transfer_rule]:
  "bi_unique A \<Longrightarrow> (LM' A ===> LM' A ===> op =) (op \<approx>) (op =)"
  "(LM' A ===> LM' A ===> LM' A) append (op +)"
  "(LM' A ===> op =) length size"
  "((A ===> B) ===> LM' A ===> LM' B) map image_mset"
  "bi_total A \<Longrightarrow> bi_total (LM' A)"
  "(LM' (LM' A) ===> LM' A) concat union_mset"
  sorry

lemma "\<forall>f xss. image_mset f (union_mset xss) =
    union_mset (image_mset (image_mset f) xss)"
  apply transfer
  sorry

lemma "\<forall>xsss. union_mset (union_mset xsss) =
    union_mset (image_mset union_mset xsss)"
  apply transfer
  sorry




end
