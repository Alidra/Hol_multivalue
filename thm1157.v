Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1157_term_abbrevs.
Require Import thm37_spec.
Require Import thm43_spec.
Lemma lem1137 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1138 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1139 (b : Prop) (a : Prop) : term0 b a.
Proof. exact (@lem43 b a). Qed.
Lemma lem1141 (a : Prop) (b : Prop) : term1 a b.
Proof. exact (@lem37 a b). Qed.
Lemma lem1144 (a : Prop) (b : Prop) (h1 : a = b) : b -> a.
Proof. exact (@lem1139 b a (@lem1137 a b h1)). Qed.
Lemma lem1145 (a : Prop) (b : Prop) (h1 : a = b) : a -> b.
Proof. exact (@lem1141 a b (@lem1137 a b h1)). Qed.
Lemma lem1147 (a : Prop) (b : Prop) (h1 : a -> b) : a -> b.
Proof. exact (h1). Qed.
Lemma lem1148 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1149 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (@lem1147 a b h2 (@lem1148 a h1)). Qed.
Lemma lem1150 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem1149 a b h1 h2) (fun h3 : b => @lem1138 a h1)). Qed.
Lemma lem1151 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (EQ_MP (@lem1150 a b h1 h2) (@lem1138 a h1)). Qed.
Lemma lem1152 (b : Prop) (a : Prop) (h1 : a) : term2 a b.
Proof. exact (fun h0 : a -> b => @lem1151 a b h1 h0). Qed.
Lemma lem1153 (b : Prop) (a : Prop) (h1 : a) : term3 a b.
Proof. exact (fun h0 : b -> a => @lem1152 b a h1). Qed.
Lemma lem1154 (a : Prop) (b : Prop) (h1 : a) (h2 : a = b) : term2 a b.
Proof. exact (@lem1153 b a h1 (@lem1144 a b h2)). Qed.
Lemma lem1155 (a : Prop) (b : Prop) (h1 : a) (h2 : a = b) : b.
Proof. exact (@lem1154 a b h1 h2 (@lem1145 a b h2)). Qed.
Lemma lem1156 (a : Prop) (b : Prop) (h1 : a = b) : a -> b.
Proof. exact (fun h0 : a => @lem1155 a b h0 h1). Qed.
Lemma lem1157 (a : Prop) (b : Prop) : term1 a b.
Proof. exact (fun h0 : a = b => @lem1156 a b h0). Qed.
