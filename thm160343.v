Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm160343_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm159136_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem159521 (n : nat) (m : nat) (h1 : term0 n m) : term0 n m.
Proof. exact (h1). Qed.
Lemma lem159524 (n : nat) (m : nat) (h1 : term1 n m) : term1 n m.
Proof. exact (h1). Qed.
Lemma lem159525 (n : nat) (m : nat) : term2 n m.
Proof. exact (fun h0 : term1 n m => @lem159524 n m h0). Qed.
Lemma lem159526 (n : nat) (m : nat) (h1 : term2 n m) : term2 n m.
Proof. exact (h1). Qed.
Lemma lem159527 (n : nat) (m : nat) (h1 : term1 n m) : term1 n m.
Proof. exact (h1). Qed.
Lemma lem159528 (n : nat) (m : nat) (h1 : term1 n m) (h2 : term2 n m) : term1 n m.
Proof. exact (@lem159526 n m h2 (@lem159527 n m h1)). Qed.
Lemma lem159529 (n : nat) (m : nat) (h1 : term1 n m) : term3 n m.
Proof. exact (fun h0 : term2 n m => @lem159528 n m h1 h0). Qed.
Lemma lem159530 (n : nat) (m : nat) (h1 : term2 n m) : term2 n m.
Proof. exact (h1). Qed.
Lemma lem159531 (n : nat) (m : nat) (h1 : term1 n m) (h2 : term2 n m) : term1 n m.
Proof. exact (@lem159529 n m h1 (@lem159530 n m h2)). Qed.
Lemma lem159532 (n : nat) (m : nat) (h1 : term2 n m) : term2 n m.
Proof. exact (fun h0 : term1 n m => @lem159531 n m h0 h1). Qed.
Lemma lem159533 (n : nat) (m : nat) : term4 n m.
Proof. exact (fun h0 : term2 n m => @lem159532 n m h0). Qed.
Lemma lem159536 (n : nat) (m : nat) : term2 n m.
Proof. exact (@lem159533 n m (@lem159525 n m)). Qed.
Lemma lem159560 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem159561 : term5 = term6.
Proof. exact (@lem159560 term7). Qed.
Lemma lem159574 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem159575 : term9 = term10.
Proof. exact (MK_COMB (@lem159574) (@lem159561)). Qed.
Lemma lem159578 (n : nat) (m : nat) : (term11 n m) = (term11 n m).
Proof. exact (eq_refl (term11 n m)). Qed.
Lemma lem159579 (n : nat) (m : nat) : (term12 n m) = (term13 n m).
Proof. exact (MK_COMB (@lem159578 n m) (@lem159575)). Qed.
Lemma lem159582 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem159583 (n : nat) (m : nat) : (term1 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem159582 n) (@lem159579 n m)). Qed.
Lemma lem159586 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem159583 n m)). Qed.
Lemma lem159587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159588 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem159587) (@lem159586 m)). Qed.
Lemma lem159593 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem159588 m)). Qed.
Lemma lem159594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159603 : term22 = term23.
Proof. exact (MK_COMB (@lem159594) (@lem159593)). Qed.
Lemma lem159614 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem159615 (m : nat) : (term25 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem159614 m n)). Qed.
Lemma lem159616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159617 (m : nat) : (term26 m) = (term26 m).
Proof. exact (MK_COMB (@lem159616) (@lem159615 m)). Qed.
Lemma lem159618 : term27 = term27.
Proof. exact (fun_ext (fun m : nat => @lem159617 m)). Qed.
Lemma lem159619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159620 : term7 = term7.
Proof. exact (MK_COMB (@lem159619) (@lem159618)). Qed.
Lemma lem159621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem159622 : term6 = term6.
Proof. exact (MK_COMB (@lem159621) (@lem159620)). Qed.
Lemma lem159623 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem159624 (m : nat) : (term28 m) = (term28 m).
Proof. exact (fun_ext (fun n : nat => @lem159623 n m)). Qed.
Lemma lem159625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159626 (m : nat) : (term29 m) = (term29 m).
Proof. exact (MK_COMB (@lem159625) (@lem159624 m)). Qed.
Lemma lem159627 : term30 = term30.
Proof. exact (fun_ext (fun m : nat => @lem159626 m)). Qed.
Lemma lem159628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159629 : term31 = term31.
Proof. exact (MK_COMB (@lem159628) (@lem159627)). Qed.
Lemma lem159630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem159631 : term8 = term8.
Proof. exact (MK_COMB (@lem159630) (@lem159629)). Qed.
Lemma lem159632 : term10 = term10.
Proof. exact (MK_COMB (@lem159631) (@lem159622)). Qed.
Lemma lem159637 (n : nat) (m : nat) : (term11 n m) = (term11 n m).
Proof. exact (eq_refl (term11 n m)). Qed.
Lemma lem159638 (n : nat) (m : nat) : (term13 n m) = (term13 n m).
Proof. exact (MK_COMB (@lem159637 n m) (@lem159632)). Qed.
Lemma lem159643 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem159644 (n : nat) (m : nat) : (term15 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem159643 n) (@lem159638 n m)). Qed.
Lemma lem159645 (m : nat) : (term17 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem159644 n m)). Qed.
Lemma lem159646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159647 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem159646) (@lem159645 m)). Qed.
Lemma lem159648 : term21 = term21.
Proof. exact (fun_ext (fun m : nat => @lem159647 m)). Qed.
Lemma lem159649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159650 : term23 = term23.
Proof. exact (MK_COMB (@lem159649) (@lem159648)). Qed.
Lemma lem159699 : term22 = term23.
Proof. exact (TRANS (@lem159603) (@lem159650)). Qed.
Lemma lem159700 : term23 = term22.
Proof. exact (SYM (@lem159699)). Qed.
Lemma lem159704 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem159710 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem159716 (n : nat) (m : nat) (h1 : term0 n m) : term0 n m.
Proof. exact (h1). Qed.
Lemma lem159739 (n : nat) : (term33 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem159744 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem159745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem159746 (n : nat) : (term35 n) = (term36 n).
Proof. exact (MK_COMB (@lem159745) (@lem159739 n)). Qed.
Lemma lem159747 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem159746 n) (@lem159744 m n)). Qed.
Lemma lem159748 (m : nat) (n : nat) : (term24 m n) = (term37 m n).
Proof. exact (@lem17265 (term32 n) (term34 m n)). Qed.
Lemma lem159749 (m : nat) (n : nat) : (term24 m n) = (term38 m n).
Proof. exact (TRANS (@lem159748 m n) (@lem159747 m n)). Qed.
Lemma lem159750 (m : nat) : (term25 m) = (term39 m).
Proof. exact (fun_ext (fun n : nat => @lem159749 m n)). Qed.
Lemma lem159751 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159752 (m : nat) : (term26 m) = (term40 m).
Proof. exact (MK_COMB (@lem159751) (@lem159750 m)). Qed.
Lemma lem159753 : term27 = term41.
Proof. exact (fun_ext (fun m : nat => @lem159752 m)). Qed.
Lemma lem159754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159811 : term7 = term42.
Proof. exact (MK_COMB (@lem159754) (@lem159753)). Qed.
Lemma lem159812 (h1 : term7) : term42.
Proof. exact (EQ_MP (@lem159811) (@lem159704 h1)). Qed.
Lemma lem159822 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem159846 (n : nat) (m : nat) (h1 : term0 n m) : term0 n m.
Proof. exact (h1). Qed.
Lemma lem159909 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem159910 (m : nat) : (term39 m) = (term39 m).
Proof. exact (fun_ext (fun n : nat => @lem159909 m n)). Qed.
Lemma lem159911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159912 (m : nat) : (term40 m) = (term40 m).
Proof. exact (MK_COMB (@lem159911) (@lem159910 m)). Qed.
Lemma lem159913 : term41 = term41.
Proof. exact (fun_ext (fun m : nat => @lem159912 m)). Qed.
Lemma lem159914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159915 : term42 = term42.
Proof. exact (MK_COMB (@lem159914) (@lem159913)). Qed.
Lemma lem159916 (h1 : term7) : term42.
Proof. exact (EQ_MP (@lem159915) (@lem159812 h1)). Qed.
Lemma lem159920 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem159924 (n : nat) (m : nat) (h1 : term0 n m) : term0 n m.
Proof. exact (h1). Qed.
Lemma lem159952 (m : nat) (n : nat) : (term38 m n) = (term43 m n).
Proof. exact (@lem19490 (m = (term44 m n)) (n = (NUMERAL 0)) (term45 m n)). Qed.
Lemma lem159953 (m : nat) : (term39 m) = (term46 m).
Proof. exact (fun_ext (fun n : nat => @lem159952 m n)). Qed.
Lemma lem159954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159955 (m : nat) : (term40 m) = (term47 m).
Proof. exact (MK_COMB (@lem159954) (@lem159953 m)). Qed.
Lemma lem159956 : term41 = term48.
Proof. exact (fun_ext (fun m : nat => @lem159955 m)). Qed.
Lemma lem159957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem159959 : term42 = term49.
Proof. exact (MK_COMB (@lem159957) (@lem159956)). Qed.
Lemma lem159960 (h1 : term7) : term49.
Proof. exact (EQ_MP (@lem159959) (@lem159916 h1)). Qed.
Lemma lem159967 (_3194 : nat) (h1 : term7) : term50 _3194.
Proof. exact (@lem159960 h1 _3194). Qed.
Lemma lem159968 (_3194 : nat) : (term50 _3194) = (term47 _3194).
Proof. exact (eq_refl (term50 _3194)). Qed.
Lemma lem159969 (_3194 : nat) (h1 : term7) : term47 _3194.
Proof. exact (EQ_MP (@lem159968 _3194) (@lem159967 _3194 h1)). Qed.
Lemma lem159970 (_3194 : nat) (_3195 : nat) (h1 : term7) : term51 _3194 _3195.
Proof. exact (@lem159969 _3194 h1 _3195). Qed.
Lemma lem159971 (_3194 : nat) (_3195 : nat) : (term51 _3194 _3195) = (term43 _3194 _3195).
Proof. exact (eq_refl (term51 _3194 _3195)). Qed.
Lemma lem159972 (_3194 : nat) (_3195 : nat) (h1 : term7) : term43 _3194 _3195.
Proof. exact (EQ_MP (@lem159971 _3194 _3195) (@lem159970 _3194 _3195 h1)). Qed.
Lemma lem159976 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem159978 (n : nat) (m : nat) (h1 : term0 n m) : term0 n m.
Proof. exact (h1). Qed.
Lemma lem159986 (_3194 : nat) (_3195 : nat) (h1 : term7) : term52 _3194 _3195.
Proof. exact (proj1 (@lem159972 _3194 _3195 h1)). Qed.
Lemma lem160081 (x : nat) (y : nat) (z : nat) : term53 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem160083 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem160084 (n : nat) (h1 : term32 n) : term54 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem160083 n h1). Qed.
Lemma lem160086 (p : Prop) : (term55 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem160087 (n : nat) : (term54 n) = (term32 n).
Proof. exact (@lem160086 (n = (NUMERAL 0))). Qed.
Lemma lem160088 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (EQ_MP (@lem160087 n) (@lem160084 n h1)). Qed.
Lemma lem160094 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem160095 (_3194 : nat) (_3195 : nat) : (term52 _3194 _3195) = (term56 _3194 _3195).
Proof. exact (@lem160094 (_3194 = (term44 _3194 _3195)) (_3195 = (NUMERAL 0))). Qed.
Lemma lem160105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem160106 (_3194 : nat) (_3195 : nat) : (term57 _3194 _3195) = (term58 _3194 _3195).
Proof. exact (MK_COMB (@lem160105) (@lem160095 _3194 _3195)). Qed.
Lemma lem160116 (_3194 : nat) (_3195 : nat) : (term56 _3194 _3195) = (term56 _3194 _3195).
Proof. exact (eq_refl (term56 _3194 _3195)). Qed.
Lemma lem160117 (_3194 : nat) (_3195 : nat) : ((term52 _3194 _3195) = (term56 _3194 _3195)) = ((term56 _3194 _3195) = (term56 _3194 _3195)).
Proof. exact (MK_COMB (@lem160106 _3194 _3195) (@lem160116 _3194 _3195)). Qed.
Lemma lem160119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem160120 (x : Prop) : (x = x) = True.
Proof. exact (@lem160119 Prop x). Qed.
Lemma lem160121 (_3194 : nat) (_3195 : nat) : ((term56 _3194 _3195) = (term56 _3194 _3195)) = True.
Proof. exact (@lem160120 (term56 _3194 _3195)). Qed.
Lemma lem160122 (_3194 : nat) (_3195 : nat) : ((term52 _3194 _3195) = (term56 _3194 _3195)) = True.
Proof. exact (TRANS (@lem160117 _3194 _3195) (@lem160121 _3194 _3195)). Qed.
Lemma lem160123 (_3194 : nat) (_3195 : nat) : True = ((term52 _3194 _3195) = (term56 _3194 _3195)).
Proof. exact (SYM (@lem160122 _3194 _3195)). Qed.
Lemma lem160124 (_3194 : nat) (_3195 : nat) : (term52 _3194 _3195) = (term56 _3194 _3195).
Proof. exact (EQ_MP (@lem160123 _3194 _3195) (@lem0)). Qed.
Lemma lem160125 (_3194 : nat) (_3195 : nat) (h1 : term7) : term56 _3194 _3195.
Proof. exact (EQ_MP (@lem160124 _3194 _3195) (@lem159986 _3194 _3195 h1)). Qed.
Lemma lem160127 (b : Prop) (a : Prop) : (a \/ b) = (term59 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem160130 (_3194 : nat) (_3195 : nat) : (term56 _3194 _3195) = (term60 _3194 _3195).
Proof. exact (@lem160127 (_3195 = (NUMERAL 0)) (_3194 = (term44 _3194 _3195))). Qed.
Lemma lem160133 (_3194 : nat) (_3195 : nat) (h1 : term7) : term60 _3194 _3195.
Proof. exact (EQ_MP (@lem160130 _3194 _3195) (@lem160125 _3194 _3195 h1)). Qed.
Lemma lem160134 (_3194 : nat) (n : nat) (h1 : term7) : term60 _3194 n.
Proof. exact (@lem160133 _3194 n h1). Qed.
Lemma lem160137 (_3194 : nat) (n : nat) (h1 : term7) (h2 : term32 n) : _3194 = (term44 _3194 n).
Proof. exact (@lem160134 _3194 n h1 (@lem160088 n h2)). Qed.
Lemma lem160138 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : m = (term44 m n).
Proof. exact (@lem160137 m n h1 h2). Qed.
Lemma lem160139 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : term61 m n.
Proof. exact (fun h0 : term62 m n => @lem160138 m n h1 h2). Qed.
Lemma lem160141 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160142 (m : nat) (n : nat) : (term61 m n) = (m = (term44 m n)).
Proof. exact (@lem160141 (m = (term44 m n))). Qed.
Lemma lem160143 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : m = (term44 m n).
Proof. exact (EQ_MP (@lem160142 m n) (@lem160139 m n h1 h2)). Qed.
Lemma lem160145 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem160146 (m : nat) : m = m.
Proof. exact (@lem160145 m). Qed.
Lemma lem160147 (m : nat) : term64 m.
Proof. exact (fun h0 : term65 m => @lem160146 m). Qed.
Lemma lem160149 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160150 (m : nat) : (term64 m) = (m = m).
Proof. exact (@lem160149 (m = m)). Qed.
Lemma lem160151 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem160150 m) (@lem160147 m)). Qed.
Lemma lem160169 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem160170 (y : nat) (x : nat) (z : nat) : (term66 x y z) = (term67 y x z).
Proof. exact (@lem160169 (y = z) (term68 x z)). Qed.
Lemma lem160180 (x : nat) (y : nat) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem160181 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term70 y x z).
Proof. exact (MK_COMB (@lem160180 x y) (@lem160170 y x z)). Qed.
Lemma lem160185 (q : Prop) (p : Prop) (r : Prop) : (term71 p q r) = (term71 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem160186 (y : nat) (x : nat) (z : nat) : (term70 y x z) = (term72 y x z).
Proof. exact (@lem160185 (y = z) (term68 x y) (term68 x z)). Qed.
Lemma lem160208 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term72 y x z).
Proof. exact (TRANS (@lem160181 y x z) (@lem160186 y x z)). Qed.
Lemma lem160209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem160210 (y : nat) (x : nat) (z : nat) : (term73 x y z) = (term74 y x z).
Proof. exact (MK_COMB (@lem160209) (@lem160208 y x z)). Qed.
Lemma lem160232 (y : nat) (x : nat) (z : nat) : (term72 y x z) = (term72 y x z).
Proof. exact (eq_refl (term72 y x z)). Qed.
Lemma lem160233 (y : nat) (x : nat) (z : nat) : ((term53 x y z) = (term72 y x z)) = ((term72 y x z) = (term72 y x z)).
Proof. exact (MK_COMB (@lem160210 y x z) (@lem160232 y x z)). Qed.
Lemma lem160235 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem160236 (x : Prop) : (x = x) = True.
Proof. exact (@lem160235 Prop x). Qed.
Lemma lem160237 (y : nat) (x : nat) (z : nat) : ((term72 y x z) = (term72 y x z)) = True.
Proof. exact (@lem160236 (term72 y x z)). Qed.
Lemma lem160238 (y : nat) (x : nat) (z : nat) : ((term53 x y z) = (term72 y x z)) = True.
Proof. exact (TRANS (@lem160233 y x z) (@lem160237 y x z)). Qed.
Lemma lem160239 (y : nat) (x : nat) (z : nat) : True = ((term53 x y z) = (term72 y x z)).
Proof. exact (SYM (@lem160238 y x z)). Qed.
Lemma lem160240 (y : nat) (x : nat) (z : nat) : (term53 x y z) = (term72 y x z).
Proof. exact (EQ_MP (@lem160239 y x z) (@lem0)). Qed.
Lemma lem160241 (y : nat) (x : nat) (z : nat) : term72 y x z.
Proof. exact (EQ_MP (@lem160240 y x z) (@lem160081 x y z)). Qed.
Lemma lem160243 (b : Prop) (a : Prop) : (a \/ b) = (term59 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem160244 (x : nat) (y : nat) (z : nat) : (term72 y x z) = (term75 x y z).
Proof. exact (@lem160243 (term76 y x z) (y = z)). Qed.
Lemma lem160246 (a : Prop) (b : Prop) : (term77 a b) = (term78 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem160247 (y : nat) (x : nat) (z : nat) : (term79 y x z) = (term80 y x z).
Proof. exact (@lem160246 (term68 x y) (term68 x z)). Qed.
Lemma lem160249 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem160250 (x : nat) (y : nat) : (term82 x y) = (x = y).
Proof. exact (@lem160249 (x = y)). Qed.
Lemma lem160251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem160252 (x : nat) (y : nat) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem160251) (@lem160250 x y)). Qed.
Lemma lem160254 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem160255 (x : nat) (z : nat) : (term82 x z) = (x = z).
Proof. exact (@lem160254 (x = z)). Qed.
Lemma lem160256 (y : nat) (x : nat) (z : nat) : (term80 y x z) = (term85 y x z).
Proof. exact (MK_COMB (@lem160252 x y) (@lem160255 x z)). Qed.
Lemma lem160257 (y : nat) (x : nat) (z : nat) : (term79 y x z) = (term85 y x z).
Proof. exact (TRANS (@lem160247 y x z) (@lem160256 y x z)). Qed.
Lemma lem160258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem160259 (y : nat) (x : nat) (z : nat) : (term86 y x z) = (term87 y x z).
Proof. exact (MK_COMB (@lem160258) (@lem160257 y x z)). Qed.
Lemma lem160260 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem160261 (x : nat) (y : nat) (z : nat) : (term75 x y z) = (term88 x y z).
Proof. exact (MK_COMB (@lem160259 y x z) (@lem160260 y z)). Qed.
Lemma lem160262 (x : nat) (y : nat) (z : nat) : (term72 y x z) = (term88 x y z).
Proof. exact (TRANS (@lem160244 x y z) (@lem160261 x y z)). Qed.
Lemma lem160264 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : term89 n m.
Proof. exact (conj (@lem160143 m n h1 h2) (@lem160151 m)). Qed.
Lemma lem160266 (x : nat) (y : nat) (z : nat) : term88 x y z.
Proof. exact (EQ_MP (@lem160262 x y z) (@lem160241 y x z)). Qed.
Lemma lem160267 (n : nat) (m : nat) : term90 n m.
Proof. exact (@lem160266 m (term44 m n) m). Qed.
Lemma lem160270 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : (term44 m n) = m.
Proof. exact (@lem160267 n m (@lem160264 m n h1 h2)). Qed.
Lemma lem160271 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : term91 n m.
Proof. exact (fun h0 : term0 n m => @lem160270 m n h1 h2). Qed.
Lemma lem160273 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160274 (n : nat) (m : nat) : (term91 n m) = ((term44 m n) = m).
Proof. exact (@lem160273 ((term44 m n) = m)). Qed.
Lemma lem160275 (m : nat) (n : nat) (h1 : term7) (h2 : term32 n) : (term44 m n) = m.
Proof. exact (EQ_MP (@lem160274 n m) (@lem160271 m n h1 h2)). Qed.
Lemma lem160278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem160280 (n : nat) (m : nat) : (term0 n m) = (term92 n m).
Proof. exact (@lem160278 ((term44 m n) = m)). Qed.
Lemma lem160283 (n : nat) (m : nat) (h1 : term0 n m) : term92 n m.
Proof. exact (EQ_MP (@lem160280 n m) (@lem159978 n m h1)). Qed.
Lemma lem160286 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (@lem160283 n m h3 (@lem160275 m n h1 h2)). Qed.
Lemma lem160287 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : term93.
Proof. exact (fun h0 : ~ False => @lem160286 n m h1 h2 h3). Qed.
Lemma lem160289 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160290 : term93 = False.
Proof. exact (@lem160289 False). Qed.
Lemma lem160291 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160290) (@lem160287 n m h1 h2 h3)). Qed.
Lemma lem160292 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h4 : term0 n m => @lem160291 n m h1 h2 h3) (fun h4 : False => @lem159978 n m h3)). Qed.
Lemma lem160293 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160292 n m h1 h2 h3) (@lem159978 n m h3)). Qed.
Lemma lem160294 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term32 n) = False.
Proof. exact (prop_ext (fun h4 : term32 n => @lem160293 n m h1 h2 h3) (fun h4 : False => @lem159976 n h2)). Qed.
Lemma lem160295 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160294 n m h1 h2 h3) (@lem159976 n h2)). Qed.
Lemma lem160296 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h4 : term0 n m => @lem160295 n m h1 h2 h3) (fun h4 : False => @lem159924 n m h3)). Qed.
Lemma lem160297 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160296 n m h1 h2 h3) (@lem159924 n m h3)). Qed.
Lemma lem160298 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term32 n) = False.
Proof. exact (prop_ext (fun h4 : term32 n => @lem160297 n m h1 h2 h3) (fun h4 : False => @lem159920 n h2)). Qed.
Lemma lem160299 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160298 n m h1 h2 h3) (@lem159920 n h2)). Qed.
Lemma lem160300 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h4 : term0 n m => @lem160299 n m h1 h2 h3) (fun h4 : False => @lem159924 n m h3)). Qed.
Lemma lem160301 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160300 n m h1 h2 h3) (@lem159924 n m h3)). Qed.
Lemma lem160302 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term32 n) = False.
Proof. exact (prop_ext (fun h4 : term32 n => @lem160301 n m h1 h2 h3) (fun h4 : False => @lem159920 n h2)). Qed.
Lemma lem160303 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160302 n m h1 h2 h3) (@lem159920 n h2)). Qed.
Lemma lem160304 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h4 : term0 n m => @lem160303 n m h1 h2 h3) (fun h4 : False => @lem159846 n m h3)). Qed.
Lemma lem160305 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160304 n m h1 h2 h3) (@lem159846 n m h3)). Qed.
Lemma lem160306 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term32 n) = False.
Proof. exact (prop_ext (fun h4 : term32 n => @lem160305 n m h1 h2 h3) (fun h4 : False => @lem159822 n h2)). Qed.
Lemma lem160307 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160306 n m h1 h2 h3) (@lem159822 n h2)). Qed.
Lemma lem160308 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h4 : term0 n m => @lem160307 n m h1 h2 h3) (fun h4 : False => @lem159716 n m h3)). Qed.
Lemma lem160309 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160308 n m h1 h2 h3) (@lem159716 n m h3)). Qed.
Lemma lem160310 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : (term32 n) = False.
Proof. exact (prop_ext (fun h4 : term32 n => @lem160309 n m h1 h2 h3) (fun h4 : False => @lem159710 n h2)). Qed.
Lemma lem160311 (n : nat) (m : nat) (h1 : term7) (h2 : term32 n) (h3 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160310 n m h1 h2 h3) (@lem159710 n h2)). Qed.
Lemma lem160312 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : term5.
Proof. exact (fun h0 : term7 => @lem160311 n m h0 h1 h2). Qed.
Lemma lem160313 : term5 = term6.
Proof. exact (@lem69 term7). Qed.
Lemma lem160314 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : term6.
Proof. exact (EQ_MP (@lem160313) (@lem160312 n m h1 h2)). Qed.
Lemma lem160315 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : term10.
Proof. exact (fun h0 : term31 => @lem160314 n m h1 h2). Qed.
Lemma lem160316 (m : nat) (n : nat) (h1 : term32 n) : term13 n m.
Proof. exact (fun h0 : term0 n m => @lem160315 n m h1 h0). Qed.
Lemma lem160317 (n : nat) (m : nat) : term15 n m.
Proof. exact (fun h0 : term32 n => @lem160316 m n h0). Qed.
Lemma lem160322 (m : nat) : term19 m.
Proof. exact (fun n : nat => @lem160317 n m). Qed.
Lemma lem160327 : term23.
Proof. exact (fun m : nat => @lem160322 m). Qed.
Lemma lem160328 : term22.
Proof. exact (EQ_MP (@lem159700) (@lem160327)). Qed.
Lemma lem160329 (m : nat) : term94 m.
Proof. exact (@lem160328 m). Qed.
Lemma lem160330 (m : nat) : (term94 m) = (term18 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem160331 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem160330 m) (@lem160329 m)). Qed.
Lemma lem160332 (m : nat) (n : nat) : term95 m n.
Proof. exact (@lem160331 m n). Qed.
Lemma lem160333 (n : nat) (m : nat) : (term95 m n) = (term1 n m).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem160334 (n : nat) (m : nat) : term1 n m.
Proof. exact (EQ_MP (@lem160333 n m) (@lem160332 m n)). Qed.
Lemma lem160336 (n : nat) (m : nat) : term1 n m.
Proof. exact (@lem159536 n m (@lem160334 n m)). Qed.
Lemma lem160337 (m : nat) (n : nat) (h1 : term32 n) : term12 n m.
Proof. exact (@lem160336 n m (@lem159136 n h1)). Qed.
Lemma lem160338 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : term9.
Proof. exact (@lem160337 m n h1 (@lem159521 n m h2)). Qed.
Lemma lem160339 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : term5.
Proof. exact (@lem160338 n m h1 h2 (@lem81820)). Qed.
Lemma lem160340 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : False.
Proof. exact (@lem160339 n m h1 h2 (@lem157261)). Qed.
Lemma lem160341 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : (term0 n m) = False.
Proof. exact (prop_ext (fun h3 : term0 n m => @lem160340 n m h1 h2) (fun h3 : False => @lem159521 n m h2)). Qed.
Lemma lem160342 (n : nat) (m : nat) (h1 : term32 n) (h2 : term0 n m) : False.
Proof. exact (EQ_MP (@lem160341 n m h1 h2) (@lem159521 n m h2)). Qed.
Lemma lem160343 (m : nat) (n : nat) (h1 : term32 n) : term96 n m.
Proof. exact (fun h0 : term0 n m => @lem160342 n m h1 h0). Qed.
