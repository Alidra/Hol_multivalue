Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PRE_ELIM_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm76885_spec.
Require Import thm82_spec.
Lemma lem245942 : term0.
Proof. exact (proj2 (@lem76885)). Qed.
Lemma lem245943 (n : nat) : term1 n.
Proof. exact (@lem245942 n). Qed.
Lemma lem245944 (n : nat) : (term1 n) = ((term2 n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem245947 (m : nat) : term3 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem245948 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem245949 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem245948 m) (@lem245947 m)). Qed.
Lemma lem245950 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem245949 m n). Qed.
Lemma lem245951 (m : nat) (n : nat) : (term5 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem245953 (n : nat) : term6 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem245954 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem245955 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem245954 n) (@lem245953 n)). Qed.
Lemma lem245956 (n : nat) : term8 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem245959 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem245960 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem245959 n h1)). Qed.
Lemma lem245961 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem245962 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem245961 n h1)). Qed.
Lemma lem245963 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem245960 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem245962 n h1)). Qed.
Lemma lem245964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem245965 (n : nat) : (term7 n) = (term9 n).
Proof. exact (MK_COMB (@lem245964) (@lem245963 n)). Qed.
Lemma lem245966 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem245965 n) (@lem245955 n)). Qed.
Lemma lem245967 (n : nat) : term10 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem245970 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem245971 (P : nat -> Prop) : term12 P.
Proof. exact (@lem245970 (term13 P)). Qed.
Lemma lem245972 (P : nat -> Prop) : (term14 P) = ((term15 P) = (term16 P)).
Proof. exact (eq_refl (term14 P)). Qed.
Lemma lem245973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem245974 (P : nat -> Prop) : (term17 P) = (term18 P).
Proof. exact (MK_COMB (@lem245973) (@lem245972 P)). Qed.
Lemma lem245975 (n : nat) (P : nat -> Prop) : (term19 P n) = ((term20 P n) = (term21 n P)).
Proof. exact (eq_refl (term19 P n)). Qed.
Lemma lem245976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245977 (n : nat) (P : nat -> Prop) : (term22 P n) = (term23 n P).
Proof. exact (MK_COMB (@lem245976) (@lem245975 n P)). Qed.
Lemma lem245978 (n : nat) (P : nat -> Prop) : (term24 P n) = ((term25 P n) = (term26 n P)).
Proof. exact (eq_refl (term24 P n)). Qed.
Lemma lem245979 (n : nat) (P : nat -> Prop) : (term27 P n) = (term28 n P).
Proof. exact (MK_COMB (@lem245977 n P) (@lem245978 n P)). Qed.
Lemma lem245980 (P : nat -> Prop) : (term29 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem245979 n P)). Qed.
Lemma lem245981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem245982 (P : nat -> Prop) : (term31 P) = (term32 P).
Proof. exact (MK_COMB (@lem245981) (@lem245980 P)). Qed.
Lemma lem245983 (P : nat -> Prop) : (term33 P) = (term34 P).
Proof. exact (MK_COMB (@lem245974 P) (@lem245982 P)). Qed.
Lemma lem245984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem245985 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (MK_COMB (@lem245984) (@lem245983 P)). Qed.
Lemma lem245986 (n : nat) (P : nat -> Prop) : (term19 P n) = ((term20 P n) = (term21 n P)).
Proof. exact (eq_refl (term19 P n)). Qed.
Lemma lem245987 (P : nat -> Prop) : (term37 P) = (term13 P).
Proof. exact (fun_ext (fun n : nat => @lem245986 n P)). Qed.
Lemma lem245988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem245989 (P : nat -> Prop) : (term38 P) = (term39 P).
Proof. exact (MK_COMB (@lem245988) (@lem245987 P)). Qed.
Lemma lem245990 (P : nat -> Prop) : (term12 P) = (term40 P).
Proof. exact (MK_COMB (@lem245985 P) (@lem245989 P)). Qed.
Lemma lem245991 (P : nat -> Prop) : term40 P.
Proof. exact (EQ_MP (@lem245990 P) (@lem245971 P)). Qed.
Lemma lem245996 : term41 = (NUMERAL 0).
Proof. exact (proj1 (@lem76885)). Qed.
Lemma lem245997 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem245998 (P : nat -> Prop) : (term15 P) = (term42 P).
Proof. exact (MK_COMB (@lem245997 P) (@lem245996)). Qed.
Lemma lem245999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246000 (P : nat -> Prop) : (term43 P) = (term44 P).
Proof. exact (MK_COMB (@lem245999) (@lem245998 P)). Qed.
Lemma lem246010 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem245967 n (@lem245966 n)). Qed.
Lemma lem246011 (m : nat) : ((NUMERAL 0) = (S m)) = False.
Proof. exact (@lem246010 m). Qed.
Lemma lem246012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246013 (m : nat) : (term45 m) = (or False).
Proof. exact (MK_COMB (@lem246012) (@lem246011 m)). Qed.
Lemma lem246019 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem246020 (x : nat) : (x = x) = True.
Proof. exact (@lem246019 nat x). Qed.
Lemma lem246021 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem246020 (NUMERAL 0)). Qed.
Lemma lem246022 (m : nat) : (term46 m) = (term46 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem246023 (m : nat) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem246022 m) (@lem246021)). Qed.
Lemma lem246025 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem246026 (m : nat) : (term48 m) = (m = (NUMERAL 0)).
Proof. exact (@lem246025 (m = (NUMERAL 0))). Qed.
Lemma lem246029 (m : nat) : (term47 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem246023 m) (@lem246026 m)). Qed.
Lemma lem246030 (m : nat) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem246013 m) (@lem246029 m)). Qed.
Lemma lem246032 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem246033 (m : nat) : (term50 m) = (m = (NUMERAL 0)).
Proof. exact (@lem246032 (m = (NUMERAL 0))). Qed.
Lemma lem246036 (m : nat) : (term49 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem246030 m) (@lem246033 m)). Qed.
Lemma lem246037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem246038 (m : nat) : (term51 m) = (term52 m).
Proof. exact (MK_COMB (@lem246037) (@lem246036 m)). Qed.
Lemma lem246039 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem246040 (P : nat -> Prop) (m : nat) : (term53 P m) = (term54 P m).
Proof. exact (MK_COMB (@lem246038 m) (@lem246039 P m)). Qed.
Lemma lem246045 (P : nat -> Prop) : (term55 P) = (term56 P).
Proof. exact (fun_ext (fun m : nat => @lem246040 P m)). Qed.
Lemma lem246046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246047 (P : nat -> Prop) : (term16 P) = (term57 P).
Proof. exact (MK_COMB (@lem246046) (@lem246045 P)). Qed.
Lemma lem246052 (P : nat -> Prop) : ((term15 P) = (term16 P)) = ((term42 P) = (term57 P)).
Proof. exact (MK_COMB (@lem246000 P) (@lem246047 P)). Qed.
Lemma lem246055 (P : nat -> Prop) : ((term42 P) = (term57 P)) = ((term15 P) = (term16 P)).
Proof. exact (SYM (@lem246052 P)). Qed.
Lemma lem246059 (n : nat) : (term2 n) = n.
Proof. exact (EQ_MP (@lem245944 n) (@lem245943 n)). Qed.
Lemma lem246060 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem246061 (P : nat -> Prop) (n : nat) : (term25 P n) = (P n).
Proof. exact (MK_COMB (@lem246060 P) (@lem246059 n)). Qed.
Lemma lem246062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246063 (P : nat -> Prop) (n : nat) : (term58 P n) = (term59 P n).
Proof. exact (MK_COMB (@lem246062) (@lem246061 P n)). Qed.
Lemma lem246073 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem245951 m n) (@lem245950 m n)). Qed.
Lemma lem246074 (n : nat) (m : nat) : ((S n) = (S m)) = (n = m).
Proof. exact (@lem246073 n m). Qed.
Lemma lem246077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246078 (n : nat) (m : nat) : (term60 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem246077) (@lem246074 n m)). Qed.
Lemma lem246084 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem245956 n (@lem245955 n)). Qed.
Lemma lem246085 (m : nat) : (term46 m) = (term46 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem246086 (n : nat) (m : nat) : (term62 m n) = (term63 m).
Proof. exact (MK_COMB (@lem246085 m) (@lem246084 n)). Qed.
Lemma lem246088 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem246089 (m : nat) : (term63 m) = False.
Proof. exact (@lem246088 (m = (NUMERAL 0))). Qed.
Lemma lem246090 (m : nat) (n : nat) : (term62 m n) = False.
Proof. exact (TRANS (@lem246086 n m) (@lem246089 m)). Qed.
Lemma lem246091 (n : nat) (m : nat) : (term64 m n) = (term65 n m).
Proof. exact (MK_COMB (@lem246078 n m) (@lem246090 m n)). Qed.
Lemma lem246093 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem246094 (n : nat) (m : nat) : (term65 n m) = (n = m).
Proof. exact (@lem246093 (n = m)). Qed.
Lemma lem246097 (n : nat) (m : nat) : (term64 m n) = (n = m).
Proof. exact (TRANS (@lem246091 n m) (@lem246094 n m)). Qed.
Lemma lem246098 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem246099 (n : nat) (m : nat) : (term66 m n) = (term67 n m).
Proof. exact (MK_COMB (@lem246098) (@lem246097 n m)). Qed.
Lemma lem246100 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem246101 (n : nat) (P : nat -> Prop) (m : nat) : (term68 n P m) = (term69 n P m).
Proof. exact (MK_COMB (@lem246099 n m) (@lem246100 P m)). Qed.
Lemma lem246106 (n : nat) (P : nat -> Prop) : (term70 n P) = (term71 n P).
Proof. exact (fun_ext (fun m : nat => @lem246101 n P m)). Qed.
Lemma lem246107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246108 (n : nat) (P : nat -> Prop) : (term26 n P) = (term72 n P).
Proof. exact (MK_COMB (@lem246107) (@lem246106 n P)). Qed.
Lemma lem246113 (n : nat) (P : nat -> Prop) : ((term25 P n) = (term26 n P)) = ((P n) = (term72 n P)).
Proof. exact (MK_COMB (@lem246063 P n) (@lem246108 n P)). Qed.
Lemma lem246116 (n : nat) (P : nat -> Prop) : ((P n) = (term72 n P)) = ((term25 P n) = (term26 n P)).
Proof. exact (SYM (@lem246113 n P)). Qed.
Lemma lem246118 (p : Prop) : p = (term73 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem246119 (P : nat -> Prop) : ((term42 P) = (term57 P)) = (term74 P).
Proof. exact (@lem246118 ((term42 P) = (term57 P))). Qed.
Lemma lem246120 (P : nat -> Prop) : (term74 P) = ((term42 P) = (term57 P)).
Proof. exact (SYM (@lem246119 P)). Qed.
Lemma lem246121 (P : nat -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem246124 (P : nat -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem246125 (P : nat -> Prop) : term76 P.
Proof. exact (fun h0 : term74 P => @lem246124 P h0). Qed.
Lemma lem246126 (P : nat -> Prop) (h1 : term76 P) : term76 P.
Proof. exact (h1). Qed.
Lemma lem246127 (P : nat -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem246128 (P : nat -> Prop) (h1 : term74 P) (h2 : term76 P) : term74 P.
Proof. exact (@lem246126 P h2 (@lem246127 P h1)). Qed.
Lemma lem246129 (P : nat -> Prop) (h1 : term74 P) : term77 P.
Proof. exact (fun h0 : term76 P => @lem246128 P h1 h0). Qed.
Lemma lem246130 (P : nat -> Prop) (h1 : term76 P) : term76 P.
Proof. exact (h1). Qed.
Lemma lem246131 (P : nat -> Prop) (h1 : term74 P) (h2 : term76 P) : term74 P.
Proof. exact (@lem246129 P h1 (@lem246130 P h2)). Qed.
Lemma lem246132 (P : nat -> Prop) (h1 : term76 P) : term76 P.
Proof. exact (fun h0 : term74 P => @lem246131 P h0 h1). Qed.
Lemma lem246133 (P : nat -> Prop) : term78 P.
Proof. exact (fun h0 : term76 P => @lem246132 P h0). Qed.
Lemma lem246136 (P : nat -> Prop) : term76 P.
Proof. exact (@lem246133 P (@lem246125 P)). Qed.
Lemma lem246142 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem246143 (P : nat -> Prop) : (term74 P) = (term79 P).
Proof. exact (@lem246142 (term75 P)). Qed.
Lemma lem246145 (t : Prop) : (term80 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem246146 (P : nat -> Prop) : (term79 P) = ((term42 P) = (term57 P)).
Proof. exact (@lem246145 ((term42 P) = (term57 P))). Qed.
Lemma lem246147 (P : nat -> Prop) : (term74 P) = ((term42 P) = (term57 P)).
Proof. exact (TRANS (@lem246143 P) (@lem246146 P)). Qed.
Lemma lem246154 : term81 = term82.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem246147 P)). Qed.
Lemma lem246155 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem246164 : term83 = term84.
Proof. exact (MK_COMB (@lem246155) (@lem246154)). Qed.
Lemma lem246169 (P : nat -> Prop) (m : nat) : (term54 P m) = (term54 P m).
Proof. exact (eq_refl (term54 P m)). Qed.
Lemma lem246170 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (fun_ext (fun m : nat => @lem246169 P m)). Qed.
Lemma lem246171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246172 (P : nat -> Prop) : (term57 P) = (term57 P).
Proof. exact (MK_COMB (@lem246171) (@lem246170 P)). Qed.
Lemma lem246175 (P : nat -> Prop) : (term44 P) = (term44 P).
Proof. exact (eq_refl (term44 P)). Qed.
Lemma lem246176 (P : nat -> Prop) : ((term42 P) = (term57 P)) = ((term42 P) = (term57 P)).
Proof. exact (MK_COMB (@lem246175 P) (@lem246172 P)). Qed.
Lemma lem246177 : term82 = term82.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem246176 P)). Qed.
Lemma lem246178 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem246179 : term84 = term84.
Proof. exact (MK_COMB (@lem246178) (@lem246177)). Qed.
Lemma lem246196 : term83 = term84.
Proof. exact (TRANS (@lem246164) (@lem246179)). Qed.
Lemma lem246197 : term84 = term83.
Proof. exact (SYM (@lem246196)). Qed.
Lemma lem246199 (p : Prop) : p = (term73 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem246200 (P : nat -> Prop) : ((term42 P) = (term57 P)) = (term74 P).
Proof. exact (@lem246199 ((term42 P) = (term57 P))). Qed.
Lemma lem246201 (P : nat -> Prop) : (term74 P) = ((term42 P) = (term57 P)).
Proof. exact (SYM (@lem246200 P)). Qed.
Lemma lem246202 (P : nat -> Prop) (h1 : term75 P) : term75 P.
Proof. exact (h1). Qed.
Lemma lem246213 (P : nat -> Prop) (m : nat) : (term85 P m) = (term86 P m).
Proof. exact (@lem17362 (m = (NUMERAL 0)) (P m)). Qed.
Lemma lem246218 (P : nat -> Prop) (m : nat) : (term54 P m) = (term87 P m).
Proof. exact (@lem17265 (m = (NUMERAL 0)) (P m)). Qed.
Lemma lem246219 (P : nat -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem246220 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem246219 (term56 P)). Qed.
Lemma lem246221 (P : nat -> Prop) (m : nat) : (term92 P m) = (term54 P m).
Proof. exact (eq_refl (term92 P m)). Qed.
Lemma lem246222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem246223 (P : nat -> Prop) (m : nat) : (term93 P m) = (term85 P m).
Proof. exact (MK_COMB (@lem246222) (@lem246221 P m)). Qed.
Lemma lem246224 (P : nat -> Prop) (m : nat) : (term93 P m) = (term86 P m).
Proof. exact (TRANS (@lem246223 P m) (@lem246213 P m)). Qed.
Lemma lem246225 (P : nat -> Prop) : (term94 P) = (term95 P).
Proof. exact (fun_ext (fun m : nat => @lem246224 P m)). Qed.
Lemma lem246226 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246227 (P : nat -> Prop) : (term91 P) = (term96 P).
Proof. exact (MK_COMB (@lem246226) (@lem246225 P)). Qed.
Lemma lem246228 (P : nat -> Prop) : (term90 P) = (term96 P).
Proof. exact (TRANS (@lem246220 P) (@lem246227 P)). Qed.
Lemma lem246229 (P : nat -> Prop) : (term56 P) = (term97 P).
Proof. exact (fun_ext (fun m : nat => @lem246218 P m)). Qed.
Lemma lem246230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246231 (P : nat -> Prop) : (term57 P) = (term98 P).
Proof. exact (MK_COMB (@lem246230) (@lem246229 P)). Qed.
Lemma lem246233 (P : nat -> Prop) : (term99 P) = (term99 P).
Proof. exact (eq_refl (term99 P)). Qed.
Lemma lem246234 (P : nat -> Prop) : (term100 P) = (term101 P).
Proof. exact (MK_COMB (@lem246233 P) (@lem246231 P)). Qed.
Lemma lem246236 (P : nat -> Prop) : (term102 P) = (term102 P).
Proof. exact (eq_refl (term102 P)). Qed.
Lemma lem246237 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (MK_COMB (@lem246236 P) (@lem246228 P)). Qed.
Lemma lem246238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246239 (P : nat -> Prop) : (term105 P) = (term106 P).
Proof. exact (MK_COMB (@lem246238) (@lem246237 P)). Qed.
Lemma lem246240 (P : nat -> Prop) : (term107 P) = (term108 P).
Proof. exact (MK_COMB (@lem246239 P) (@lem246234 P)). Qed.
Lemma lem246241 (P : nat -> Prop) : (term75 P) = (term107 P).
Proof. exact (@lem17646 (term42 P) (term57 P)). Qed.
Lemma lem246242 (P : nat -> Prop) : (term75 P) = (term108 P).
Proof. exact (TRANS (@lem246241 P) (@lem246240 P)). Qed.
Lemma lem246325 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem246326 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem246325 nat P Q). Qed.
Lemma lem246327 (P : nat -> Prop) : (term113 P) = (term114 P).
Proof. exact (@lem246326 (term42 P) (term95 P)). Qed.
Lemma lem246328 (P : nat -> Prop) (m : nat) : (term115 P m) = (term86 P m).
Proof. exact (eq_refl (term115 P m)). Qed.
Lemma lem246329 (P : nat -> Prop) : (term116 P) = (term95 P).
Proof. exact (fun_ext (fun m : nat => @lem246328 P m)). Qed.
Lemma lem246330 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246331 (P : nat -> Prop) : (term117 P) = (term96 P).
Proof. exact (MK_COMB (@lem246330) (@lem246329 P)). Qed.
Lemma lem246332 (P : nat -> Prop) : (term102 P) = (term102 P).
Proof. exact (eq_refl (term102 P)). Qed.
Lemma lem246333 (P : nat -> Prop) : (term113 P) = (term104 P).
Proof. exact (MK_COMB (@lem246332 P) (@lem246331 P)). Qed.
Lemma lem246334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246335 (P : nat -> Prop) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem246334) (@lem246333 P)). Qed.
Lemma lem246336 (P : nat -> Prop) (m : nat) : (term115 P m) = (term86 P m).
Proof. exact (eq_refl (term115 P m)). Qed.
Lemma lem246337 (P : nat -> Prop) : (term102 P) = (term102 P).
Proof. exact (eq_refl (term102 P)). Qed.
Lemma lem246338 (P : nat -> Prop) (m : nat) : (term120 P m) = (term121 P m).
Proof. exact (MK_COMB (@lem246337 P) (@lem246336 P m)). Qed.
Lemma lem246339 (P : nat -> Prop) : (term122 P) = (term123 P).
Proof. exact (fun_ext (fun m : nat => @lem246338 P m)). Qed.
Lemma lem246340 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246341 (P : nat -> Prop) : (term114 P) = (term124 P).
Proof. exact (MK_COMB (@lem246340) (@lem246339 P)). Qed.
Lemma lem246342 (P : nat -> Prop) : ((term113 P) = (term114 P)) = ((term104 P) = (term124 P)).
Proof. exact (MK_COMB (@lem246335 P) (@lem246341 P)). Qed.
Lemma lem246343 (P : nat -> Prop) : (term104 P) = (term124 P).
Proof. exact (EQ_MP (@lem246342 P) (@lem246327 P)). Qed.
Lemma lem246344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246345 (P : nat -> Prop) : (term106 P) = (term125 P).
Proof. exact (MK_COMB (@lem246344) (@lem246343 P)). Qed.
Lemma lem246346 (P : nat -> Prop) : (term101 P) = (term101 P).
Proof. exact (eq_refl (term101 P)). Qed.
Lemma lem246347 (P : nat -> Prop) : (term108 P) = (term126 P).
Proof. exact (MK_COMB (@lem246345 P) (@lem246346 P)). Qed.
Lemma lem246349 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem246350 (P : nat -> Prop) (Q : Prop) : (term129 P Q) = (term130 P Q).
Proof. exact (@lem246349 nat P Q). Qed.
Lemma lem246351 (P : nat -> Prop) : (term131 P) = (term132 P).
Proof. exact (@lem246350 (term123 P) (term101 P)). Qed.
Lemma lem246352 (P : nat -> Prop) (m : nat) : (term133 P m) = (term121 P m).
Proof. exact (eq_refl (term133 P m)). Qed.
Lemma lem246353 (P : nat -> Prop) : (term134 P) = (term123 P).
Proof. exact (fun_ext (fun m : nat => @lem246352 P m)). Qed.
Lemma lem246354 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246355 (P : nat -> Prop) : (term135 P) = (term124 P).
Proof. exact (MK_COMB (@lem246354) (@lem246353 P)). Qed.
Lemma lem246356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246357 (P : nat -> Prop) : (term136 P) = (term125 P).
Proof. exact (MK_COMB (@lem246356) (@lem246355 P)). Qed.
Lemma lem246358 (P : nat -> Prop) : (term101 P) = (term101 P).
Proof. exact (eq_refl (term101 P)). Qed.
Lemma lem246359 (P : nat -> Prop) : (term131 P) = (term126 P).
Proof. exact (MK_COMB (@lem246357 P) (@lem246358 P)). Qed.
Lemma lem246360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246361 (P : nat -> Prop) : (term137 P) = (term138 P).
Proof. exact (MK_COMB (@lem246360) (@lem246359 P)). Qed.
Lemma lem246362 (P : nat -> Prop) (m : nat) : (term133 P m) = (term121 P m).
Proof. exact (eq_refl (term133 P m)). Qed.
Lemma lem246363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246364 (P : nat -> Prop) (m : nat) : (term139 P m) = (term140 P m).
Proof. exact (MK_COMB (@lem246363) (@lem246362 P m)). Qed.
Lemma lem246365 (P : nat -> Prop) : (term101 P) = (term101 P).
Proof. exact (eq_refl (term101 P)). Qed.
Lemma lem246366 (m : nat) (P : nat -> Prop) : (term141 m P) = (term142 m P).
Proof. exact (MK_COMB (@lem246364 P m) (@lem246365 P)). Qed.
Lemma lem246367 (P : nat -> Prop) : (term143 P) = (term144 P).
Proof. exact (fun_ext (fun m : nat => @lem246366 m P)). Qed.
Lemma lem246368 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246369 (P : nat -> Prop) : (term132 P) = (term145 P).
Proof. exact (MK_COMB (@lem246368) (@lem246367 P)). Qed.
Lemma lem246370 (P : nat -> Prop) : ((term131 P) = (term132 P)) = ((term126 P) = (term145 P)).
Proof. exact (MK_COMB (@lem246361 P) (@lem246369 P)). Qed.
Lemma lem246371 (P : nat -> Prop) : (term126 P) = (term145 P).
Proof. exact (EQ_MP (@lem246370 P) (@lem246351 P)). Qed.
Lemma lem246373 (P : nat -> Prop) : (term108 P) = (term145 P).
Proof. exact (TRANS (@lem246347 P) (@lem246371 P)). Qed.
Lemma lem246374 (P : nat -> Prop) : (term75 P) = (term145 P).
Proof. exact (TRANS (@lem246242 P) (@lem246373 P)). Qed.
Lemma lem246375 (P : nat -> Prop) (h1 : term75 P) : term145 P.
Proof. exact (EQ_MP (@lem246374 P) (@lem246202 P h1)). Qed.
Lemma lem246376 (m : nat) (P : nat -> Prop) (h1 : term142 m P) : term142 m P.
Proof. exact (h1). Qed.
Lemma lem246391 (P : nat -> Prop) (m : nat) : (term87 P m) = (term87 P m).
Proof. exact (eq_refl (term87 P m)). Qed.
Lemma lem246392 (P : nat -> Prop) : (term97 P) = (term97 P).
Proof. exact (fun_ext (fun m : nat => @lem246391 P m)). Qed.
Lemma lem246393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246394 (P : nat -> Prop) : (term98 P) = (term98 P).
Proof. exact (MK_COMB (@lem246393) (@lem246392 P)). Qed.
Lemma lem246403 (P : nat -> Prop) : (term99 P) = (term99 P).
Proof. exact (eq_refl (term99 P)). Qed.
Lemma lem246404 (P : nat -> Prop) : (term101 P) = (term101 P).
Proof. exact (MK_COMB (@lem246403 P) (@lem246394 P)). Qed.
Lemma lem246429 (P : nat -> Prop) (m : nat) : (term140 P m) = (term140 P m).
Proof. exact (eq_refl (term140 P m)). Qed.
Lemma lem246430 (m : nat) (P : nat -> Prop) : (term142 m P) = (term142 m P).
Proof. exact (MK_COMB (@lem246429 P m) (@lem246404 P)). Qed.
Lemma lem246431 (m : nat) (P : nat -> Prop) (h1 : term142 m P) : term142 m P.
Proof. exact (EQ_MP (@lem246430 m P) (@lem246376 m P h1)). Qed.
Lemma lem246432 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term121 P m.
Proof. exact (h1). Qed.
Lemma lem246433 (P : nat -> Prop) (h1 : term101 P) : term101 P.
Proof. exact (h1). Qed.
Lemma lem246434 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term86 P m.
Proof. exact (proj2 (@lem246432 P m h1)). Qed.
Lemma lem246438 (P : nat -> Prop) (h1 : term101 P) : term98 P.
Proof. exact (proj2 (@lem246433 P h1)). Qed.
Lemma lem246463 (P : nat -> Prop) (m : nat) : (term87 P m) = (term87 P m).
Proof. exact (eq_refl (term87 P m)). Qed.
Lemma lem246464 (P : nat -> Prop) : (term97 P) = (term97 P).
Proof. exact (fun_ext (fun m : nat => @lem246463 P m)). Qed.
Lemma lem246465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246467 (P : nat -> Prop) : (term98 P) = (term98 P).
Proof. exact (MK_COMB (@lem246465) (@lem246464 P)). Qed.
Lemma lem246468 (P : nat -> Prop) (h1 : term101 P) : term98 P.
Proof. exact (EQ_MP (@lem246467 P) (@lem246438 P h1)). Qed.
Lemma lem246469 (_4872 : nat) (P : nat -> Prop) (h1 : term101 P) : term146 P _4872.
Proof. exact (@lem246468 P h1 _4872). Qed.
Lemma lem246470 (P : nat -> Prop) (_4872 : nat) : (term146 P _4872) = (term87 P _4872).
Proof. exact (eq_refl (term146 P _4872)). Qed.
Lemma lem246475 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : m = (NUMERAL 0).
Proof. exact (proj1 (@lem246434 P m h1)). Qed.
Lemma lem246477 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term147 P m.
Proof. exact (proj2 (@lem246434 P m h1)). Qed.
Lemma lem246479 (P : nat -> Prop) (h1 : term101 P) : term148 P.
Proof. exact (proj1 (@lem246433 P h1)). Qed.
Lemma lem246485 (_4872 : nat) (P : nat -> Prop) (h1 : term101 P) : term87 P _4872.
Proof. exact (EQ_MP (@lem246470 P _4872) (@lem246469 _4872 P h1)). Qed.
Lemma lem246514 (P : nat -> Prop) : (term149 P) = (term149 P).
Proof. exact (eq_refl (term149 P)). Qed.
Lemma lem246515 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : (term150 P m) = (term151 P).
Proof. exact (MK_COMB (@lem246514 P) (@lem246475 P m h1)). Qed.
Lemma lem246516 (P : nat -> Prop) : (term151 P) = (term148 P).
Proof. exact (eq_refl (term151 P)). Qed.
Lemma lem246517 (P : nat -> Prop) (m : nat) : (term152 P m) = (term152 P m).
Proof. exact (eq_refl (term152 P m)). Qed.
Lemma lem246518 (m : nat) (P : nat -> Prop) : ((term150 P m) = (term151 P)) = ((term150 P m) = (term148 P)).
Proof. exact (MK_COMB (@lem246517 P m) (@lem246516 P)). Qed.
Lemma lem246519 (P : nat -> Prop) (m : nat) : (term150 P m) = (term147 P m).
Proof. exact (eq_refl (term150 P m)). Qed.
Lemma lem246520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246521 (P : nat -> Prop) (m : nat) : (term152 P m) = (term153 P m).
Proof. exact (MK_COMB (@lem246520) (@lem246519 P m)). Qed.
Lemma lem246522 (P : nat -> Prop) : (term148 P) = (term148 P).
Proof. exact (eq_refl (term148 P)). Qed.
Lemma lem246523 (m : nat) (P : nat -> Prop) : ((term150 P m) = (term148 P)) = ((term147 P m) = (term148 P)).
Proof. exact (MK_COMB (@lem246521 P m) (@lem246522 P)). Qed.
Lemma lem246524 (m : nat) (P : nat -> Prop) : ((term150 P m) = (term151 P)) = ((term147 P m) = (term148 P)).
Proof. exact (TRANS (@lem246518 m P) (@lem246523 m P)). Qed.
Lemma lem246525 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : (term147 P m) = (term148 P).
Proof. exact (EQ_MP (@lem246524 m P) (@lem246515 P m h1)). Qed.
Lemma lem246526 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term148 P.
Proof. exact (EQ_MP (@lem246525 P m h1) (@lem246477 P m h1)). Qed.
Lemma lem246528 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term42 P.
Proof. exact (proj1 (@lem246432 P m h1)). Qed.
Lemma lem246529 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term154 P.
Proof. exact (fun h0 : term148 P => @lem246528 P m h1). Qed.
Lemma lem246531 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem246532 (P : nat -> Prop) : (term154 P) = (term42 P).
Proof. exact (@lem246531 (term42 P)). Qed.
Lemma lem246533 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term42 P.
Proof. exact (EQ_MP (@lem246532 P) (@lem246529 P m h1)). Qed.
Lemma lem246536 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem246538 (P : nat -> Prop) : (term148 P) = (term156 P).
Proof. exact (@lem246536 (term42 P)). Qed.
Lemma lem246541 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term156 P.
Proof. exact (EQ_MP (@lem246538 P) (@lem246526 P m h1)). Qed.
Lemma lem246544 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : False.
Proof. exact (@lem246541 P m h1 (@lem246533 P m h1)). Qed.
Lemma lem246545 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : term157.
Proof. exact (fun h0 : ~ False => @lem246544 P m h1). Qed.
Lemma lem246547 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem246548 : term157 = False.
Proof. exact (@lem246547 False). Qed.
Lemma lem246573 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem246574 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem246573 (NUMERAL 0)). Qed.
Lemma lem246575 : term158.
Proof. exact (fun h0 : term159 => @lem246574). Qed.
Lemma lem246577 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem246578 : term158 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem246577 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem246579 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem246578) (@lem246575)). Qed.
Lemma lem246585 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem246586 (P : nat -> Prop) (_4872 : nat) : (term87 P _4872) = (term160 P _4872).
Proof. exact (@lem246585 (P _4872) (term161 _4872)). Qed.
Lemma lem246594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246595 (P : nat -> Prop) (_4872 : nat) : (term162 P _4872) = (term163 P _4872).
Proof. exact (MK_COMB (@lem246594) (@lem246586 P _4872)). Qed.
Lemma lem246603 (P : nat -> Prop) (_4872 : nat) : (term160 P _4872) = (term160 P _4872).
Proof. exact (eq_refl (term160 P _4872)). Qed.
Lemma lem246604 (P : nat -> Prop) (_4872 : nat) : ((term87 P _4872) = (term160 P _4872)) = ((term160 P _4872) = (term160 P _4872)).
Proof. exact (MK_COMB (@lem246595 P _4872) (@lem246603 P _4872)). Qed.
Lemma lem246606 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem246607 (x : Prop) : (x = x) = True.
Proof. exact (@lem246606 Prop x). Qed.
Lemma lem246608 (P : nat -> Prop) (_4872 : nat) : ((term160 P _4872) = (term160 P _4872)) = True.
Proof. exact (@lem246607 (term160 P _4872)). Qed.
Lemma lem246609 (P : nat -> Prop) (_4872 : nat) : ((term87 P _4872) = (term160 P _4872)) = True.
Proof. exact (TRANS (@lem246604 P _4872) (@lem246608 P _4872)). Qed.
Lemma lem246610 (P : nat -> Prop) (_4872 : nat) : True = ((term87 P _4872) = (term160 P _4872)).
Proof. exact (SYM (@lem246609 P _4872)). Qed.
Lemma lem246611 (P : nat -> Prop) (_4872 : nat) : (term87 P _4872) = (term160 P _4872).
Proof. exact (EQ_MP (@lem246610 P _4872) (@lem0)). Qed.
Lemma lem246612 (_4872 : nat) (P : nat -> Prop) (h1 : term101 P) : term160 P _4872.
Proof. exact (EQ_MP (@lem246611 P _4872) (@lem246485 _4872 P h1)). Qed.
Lemma lem246614 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem246615 (P : nat -> Prop) (_4872 : nat) : (term160 P _4872) = (term165 P _4872).
Proof. exact (@lem246614 (term161 _4872) (P _4872)). Qed.
Lemma lem246617 (a : Prop) : (term80 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem246618 (_4872 : nat) : (term166 _4872) = (_4872 = (NUMERAL 0)).
Proof. exact (@lem246617 (_4872 = (NUMERAL 0))). Qed.
Lemma lem246619 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem246620 (_4872 : nat) : (term167 _4872) = (term52 _4872).
Proof. exact (MK_COMB (@lem246619) (@lem246618 _4872)). Qed.
Lemma lem246621 (P : nat -> Prop) (_4872 : nat) : (P _4872) = (P _4872).
Proof. exact (eq_refl (P _4872)). Qed.
Lemma lem246622 (P : nat -> Prop) (_4872 : nat) : (term165 P _4872) = (term54 P _4872).
Proof. exact (MK_COMB (@lem246620 _4872) (@lem246621 P _4872)). Qed.
Lemma lem246623 (P : nat -> Prop) (_4872 : nat) : (term160 P _4872) = (term54 P _4872).
Proof. exact (TRANS (@lem246615 P _4872) (@lem246622 P _4872)). Qed.
Lemma lem246626 (_4872 : nat) (P : nat -> Prop) (h1 : term101 P) : term54 P _4872.
Proof. exact (EQ_MP (@lem246623 P _4872) (@lem246612 _4872 P h1)). Qed.
Lemma lem246627 (P : nat -> Prop) (h1 : term101 P) : term168 P.
Proof. exact (@lem246626 (NUMERAL 0) P h1). Qed.
Lemma lem246630 (P : nat -> Prop) (h1 : term101 P) : term42 P.
Proof. exact (@lem246627 P h1 (@lem246579)). Qed.
Lemma lem246631 (P : nat -> Prop) (h1 : term101 P) : term154 P.
Proof. exact (fun h0 : term148 P => @lem246630 P h1). Qed.
Lemma lem246633 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem246634 (P : nat -> Prop) : (term154 P) = (term42 P).
Proof. exact (@lem246633 (term42 P)). Qed.
Lemma lem246635 (P : nat -> Prop) (h1 : term101 P) : term42 P.
Proof. exact (EQ_MP (@lem246634 P) (@lem246631 P h1)). Qed.
Lemma lem246638 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem246640 (P : nat -> Prop) : (term148 P) = (term156 P).
Proof. exact (@lem246638 (term42 P)). Qed.
Lemma lem246643 (P : nat -> Prop) (h1 : term101 P) : term156 P.
Proof. exact (EQ_MP (@lem246640 P) (@lem246479 P h1)). Qed.
Lemma lem246646 (P : nat -> Prop) (h1 : term101 P) : False.
Proof. exact (@lem246643 P h1 (@lem246635 P h1)). Qed.
Lemma lem246647 (P : nat -> Prop) (h1 : term101 P) : term157.
Proof. exact (fun h0 : ~ False => @lem246646 P h1). Qed.
Lemma lem246649 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem246650 : term157 = False.
Proof. exact (@lem246649 False). Qed.
Lemma lem246651 (P : nat -> Prop) (h1 : term101 P) : False.
Proof. exact (EQ_MP (@lem246650) (@lem246647 P h1)). Qed.
Lemma lem246652 (P : nat -> Prop) (m : nat) (h1 : term121 P m) : False.
Proof. exact (EQ_MP (@lem246548) (@lem246545 P m h1)). Qed.
Lemma lem246653 (m : nat) (P : nat -> Prop) (h1 : term142 m P) : False.
Proof. exact (or_elim (@lem246431 m P h1) (fun h0 : term121 P m => @lem246652 P m h0) (fun h0 : term101 P => @lem246651 P h0)). Qed.
Lemma lem246654 (m : nat) (P : nat -> Prop) (h1 : term142 m P) : (term142 m P) = False.
Proof. exact (prop_ext (fun h2 : term142 m P => @lem246653 m P h1) (fun h2 : False => @lem246431 m P h1)). Qed.
Lemma lem246655 (m : nat) (P : nat -> Prop) (h1 : term142 m P) : False.
Proof. exact (EQ_MP (@lem246654 m P h1) (@lem246431 m P h1)). Qed.
Lemma lem246656 (P : nat -> Prop) (h1 : term75 P) : False.
Proof. exact (ex_elim (@lem246375 P h1) (fun m : nat => fun h0 : term144 P m => @lem246655 m P h0)). Qed.
Lemma lem246657 (P : nat -> Prop) (h1 : term75 P) : (term75 P) = False.
Proof. exact (prop_ext (fun h2 : term75 P => @lem246656 P h1) (fun h2 : False => @lem246202 P h1)). Qed.
Lemma lem246658 (P : nat -> Prop) (h1 : term75 P) : False.
Proof. exact (EQ_MP (@lem246657 P h1) (@lem246202 P h1)). Qed.
Lemma lem246659 (P : nat -> Prop) : term74 P.
Proof. exact (fun h0 : term75 P => @lem246658 P h0). Qed.
Lemma lem246660 (P : nat -> Prop) : (term42 P) = (term57 P).
Proof. exact (EQ_MP (@lem246201 P) (@lem246659 P)). Qed.
Lemma lem246665 : term84.
Proof. exact (fun P : nat -> Prop => @lem246660 P). Qed.
Lemma lem246666 : term83.
Proof. exact (EQ_MP (@lem246197) (@lem246665)). Qed.
Lemma lem246667 (P : nat -> Prop) : term169 P.
Proof. exact (@lem246666 P). Qed.
Lemma lem246668 (P : nat -> Prop) : (term169 P) = (term74 P).
Proof. exact (eq_refl (term169 P)). Qed.
Lemma lem246669 (P : nat -> Prop) : term74 P.
Proof. exact (EQ_MP (@lem246668 P) (@lem246667 P)). Qed.
Lemma lem246671 (P : nat -> Prop) : term74 P.
Proof. exact (@lem246136 P (@lem246669 P)). Qed.
Lemma lem246672 (P : nat -> Prop) (h1 : term75 P) : False.
Proof. exact (@lem246671 P (@lem246121 P h1)). Qed.
Lemma lem246673 (P : nat -> Prop) (h1 : term75 P) : (term75 P) = False.
Proof. exact (prop_ext (fun h2 : term75 P => @lem246672 P h1) (fun h2 : False => @lem246121 P h1)). Qed.
Lemma lem246674 (P : nat -> Prop) (h1 : term75 P) : False.
Proof. exact (EQ_MP (@lem246673 P h1) (@lem246121 P h1)). Qed.
Lemma lem246675 (P : nat -> Prop) : term74 P.
Proof. exact (fun h0 : term75 P => @lem246674 P h0). Qed.
Lemma lem246676 (P : nat -> Prop) : (term42 P) = (term57 P).
Proof. exact (EQ_MP (@lem246120 P) (@lem246675 P)). Qed.
Lemma lem246678 (p : Prop) : p = (term73 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem246679 (n : nat) (P : nat -> Prop) : ((P n) = (term72 n P)) = (term170 n P).
Proof. exact (@lem246678 ((P n) = (term72 n P))). Qed.
Lemma lem246680 (n : nat) (P : nat -> Prop) : (term170 n P) = ((P n) = (term72 n P)).
Proof. exact (SYM (@lem246679 n P)). Qed.
Lemma lem246681 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : term171 n P.
Proof. exact (h1). Qed.
Lemma lem246684 (n : nat) (P : nat -> Prop) (h1 : term170 n P) : term170 n P.
Proof. exact (h1). Qed.
Lemma lem246685 (n : nat) (P : nat -> Prop) : term172 n P.
Proof. exact (fun h0 : term170 n P => @lem246684 n P h0). Qed.
Lemma lem246686 (n : nat) (P : nat -> Prop) (h1 : term172 n P) : term172 n P.
Proof. exact (h1). Qed.
Lemma lem246687 (n : nat) (P : nat -> Prop) (h1 : term170 n P) : term170 n P.
Proof. exact (h1). Qed.
Lemma lem246688 (n : nat) (P : nat -> Prop) (h1 : term170 n P) (h2 : term172 n P) : term170 n P.
Proof. exact (@lem246686 n P h2 (@lem246687 n P h1)). Qed.
Lemma lem246689 (n : nat) (P : nat -> Prop) (h1 : term170 n P) : term173 n P.
Proof. exact (fun h0 : term172 n P => @lem246688 n P h1 h0). Qed.
Lemma lem246690 (n : nat) (P : nat -> Prop) (h1 : term172 n P) : term172 n P.
Proof. exact (h1). Qed.
Lemma lem246691 (n : nat) (P : nat -> Prop) (h1 : term170 n P) (h2 : term172 n P) : term170 n P.
Proof. exact (@lem246689 n P h1 (@lem246690 n P h2)). Qed.
Lemma lem246692 (n : nat) (P : nat -> Prop) (h1 : term172 n P) : term172 n P.
Proof. exact (fun h0 : term170 n P => @lem246691 n P h0 h1). Qed.
Lemma lem246693 (n : nat) (P : nat -> Prop) : term174 n P.
Proof. exact (fun h0 : term172 n P => @lem246692 n P h0). Qed.
Lemma lem246696 (n : nat) (P : nat -> Prop) : term172 n P.
Proof. exact (@lem246693 n P (@lem246685 n P)). Qed.
Lemma lem246706 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem246707 (n : nat) (P : nat -> Prop) : (term170 n P) = (term175 n P).
Proof. exact (@lem246706 (term171 n P)). Qed.
Lemma lem246709 (t : Prop) : (term80 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem246710 (n : nat) (P : nat -> Prop) : (term175 n P) = ((P n) = (term72 n P)).
Proof. exact (@lem246709 ((P n) = (term72 n P))). Qed.
Lemma lem246711 (n : nat) (P : nat -> Prop) : (term170 n P) = ((P n) = (term72 n P)).
Proof. exact (TRANS (@lem246707 n P) (@lem246710 n P)). Qed.
Lemma lem246718 (P : nat -> Prop) : (term176 P) = (term177 P).
Proof. exact (fun_ext (fun n : nat => @lem246711 n P)). Qed.
Lemma lem246719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246720 (P : nat -> Prop) : (term178 P) = (term179 P).
Proof. exact (MK_COMB (@lem246719) (@lem246718 P)). Qed.
Lemma lem246725 : term180 = term181.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem246720 P)). Qed.
Lemma lem246726 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem246735 : term182 = term183.
Proof. exact (MK_COMB (@lem246726) (@lem246725)). Qed.
Lemma lem246740 (n : nat) (P : nat -> Prop) (m : nat) : (term69 n P m) = (term69 n P m).
Proof. exact (eq_refl (term69 n P m)). Qed.
Lemma lem246741 (n : nat) (P : nat -> Prop) : (term71 n P) = (term71 n P).
Proof. exact (fun_ext (fun m : nat => @lem246740 n P m)). Qed.
Lemma lem246742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246743 (n : nat) (P : nat -> Prop) : (term72 n P) = (term72 n P).
Proof. exact (MK_COMB (@lem246742) (@lem246741 n P)). Qed.
Lemma lem246746 (P : nat -> Prop) (n : nat) : (term59 P n) = (term59 P n).
Proof. exact (eq_refl (term59 P n)). Qed.
Lemma lem246747 (n : nat) (P : nat -> Prop) : ((P n) = (term72 n P)) = ((P n) = (term72 n P)).
Proof. exact (MK_COMB (@lem246746 P n) (@lem246743 n P)). Qed.
Lemma lem246748 (P : nat -> Prop) : (term177 P) = (term177 P).
Proof. exact (fun_ext (fun n : nat => @lem246747 n P)). Qed.
Lemma lem246749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246750 (P : nat -> Prop) : (term179 P) = (term179 P).
Proof. exact (MK_COMB (@lem246749) (@lem246748 P)). Qed.
Lemma lem246751 : term181 = term181.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem246750 P)). Qed.
Lemma lem246752 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem246753 : term183 = term183.
Proof. exact (MK_COMB (@lem246752) (@lem246751)). Qed.
Lemma lem246776 : term182 = term183.
Proof. exact (TRANS (@lem246735) (@lem246753)). Qed.
Lemma lem246777 : term183 = term182.
Proof. exact (SYM (@lem246776)). Qed.
Lemma lem246779 (p : Prop) : p = (term73 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem246780 (n : nat) (P : nat -> Prop) : ((P n) = (term72 n P)) = (term170 n P).
Proof. exact (@lem246779 ((P n) = (term72 n P))). Qed.
Lemma lem246781 (n : nat) (P : nat -> Prop) : (term170 n P) = ((P n) = (term72 n P)).
Proof. exact (SYM (@lem246780 n P)). Qed.
Lemma lem246782 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : term171 n P.
Proof. exact (h1). Qed.
Lemma lem246793 (n : nat) (P : nat -> Prop) (m : nat) : (term184 n P m) = (term185 n P m).
Proof. exact (@lem17362 (n = m) (P m)). Qed.
Lemma lem246798 (n : nat) (P : nat -> Prop) (m : nat) : (term69 n P m) = (term186 n P m).
Proof. exact (@lem17265 (n = m) (P m)). Qed.
Lemma lem246799 (P : nat -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem246800 (n : nat) (P : nat -> Prop) : (term187 n P) = (term188 n P).
Proof. exact (@lem246799 (term71 n P)). Qed.
Lemma lem246801 (n : nat) (P : nat -> Prop) (m : nat) : (term189 n P m) = (term69 n P m).
Proof. exact (eq_refl (term189 n P m)). Qed.
Lemma lem246802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem246803 (n : nat) (P : nat -> Prop) (m : nat) : (term190 n P m) = (term184 n P m).
Proof. exact (MK_COMB (@lem246802) (@lem246801 n P m)). Qed.
Lemma lem246804 (n : nat) (P : nat -> Prop) (m : nat) : (term190 n P m) = (term185 n P m).
Proof. exact (TRANS (@lem246803 n P m) (@lem246793 n P m)). Qed.
Lemma lem246805 (n : nat) (P : nat -> Prop) : (term191 n P) = (term192 n P).
Proof. exact (fun_ext (fun m : nat => @lem246804 n P m)). Qed.
Lemma lem246806 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246807 (n : nat) (P : nat -> Prop) : (term188 n P) = (term193 n P).
Proof. exact (MK_COMB (@lem246806) (@lem246805 n P)). Qed.
Lemma lem246808 (n : nat) (P : nat -> Prop) : (term187 n P) = (term193 n P).
Proof. exact (TRANS (@lem246800 n P) (@lem246807 n P)). Qed.
Lemma lem246809 (n : nat) (P : nat -> Prop) : (term71 n P) = (term194 n P).
Proof. exact (fun_ext (fun m : nat => @lem246798 n P m)). Qed.
Lemma lem246810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246811 (n : nat) (P : nat -> Prop) : (term72 n P) = (term195 n P).
Proof. exact (MK_COMB (@lem246810) (@lem246809 n P)). Qed.
Lemma lem246813 (P : nat -> Prop) (n : nat) : (term196 P n) = (term196 P n).
Proof. exact (eq_refl (term196 P n)). Qed.
Lemma lem246814 (n : nat) (P : nat -> Prop) : (term197 n P) = (term198 n P).
Proof. exact (MK_COMB (@lem246813 P n) (@lem246811 n P)). Qed.
Lemma lem246816 (P : nat -> Prop) (n : nat) : (term199 P n) = (term199 P n).
Proof. exact (eq_refl (term199 P n)). Qed.
Lemma lem246817 (n : nat) (P : nat -> Prop) : (term200 n P) = (term201 n P).
Proof. exact (MK_COMB (@lem246816 P n) (@lem246808 n P)). Qed.
Lemma lem246818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246819 (n : nat) (P : nat -> Prop) : (term202 n P) = (term203 n P).
Proof. exact (MK_COMB (@lem246818) (@lem246817 n P)). Qed.
Lemma lem246820 (n : nat) (P : nat -> Prop) : (term204 n P) = (term205 n P).
Proof. exact (MK_COMB (@lem246819 n P) (@lem246814 n P)). Qed.
Lemma lem246821 (n : nat) (P : nat -> Prop) : (term171 n P) = (term204 n P).
Proof. exact (@lem17646 (P n) (term72 n P)). Qed.
Lemma lem246822 (n : nat) (P : nat -> Prop) : (term171 n P) = (term205 n P).
Proof. exact (TRANS (@lem246821 n P) (@lem246820 n P)). Qed.
Lemma lem246905 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem246906 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem246905 nat P Q). Qed.
Lemma lem246907 (n : nat) (P : nat -> Prop) : (term206 n P) = (term207 n P).
Proof. exact (@lem246906 (P n) (term192 n P)). Qed.
Lemma lem246908 (n : nat) (P : nat -> Prop) (m : nat) : (term208 n P m) = (term185 n P m).
Proof. exact (eq_refl (term208 n P m)). Qed.
Lemma lem246909 (n : nat) (P : nat -> Prop) : (term209 n P) = (term192 n P).
Proof. exact (fun_ext (fun m : nat => @lem246908 n P m)). Qed.
Lemma lem246910 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246911 (n : nat) (P : nat -> Prop) : (term210 n P) = (term193 n P).
Proof. exact (MK_COMB (@lem246910) (@lem246909 n P)). Qed.
Lemma lem246912 (P : nat -> Prop) (n : nat) : (term199 P n) = (term199 P n).
Proof. exact (eq_refl (term199 P n)). Qed.
Lemma lem246913 (n : nat) (P : nat -> Prop) : (term206 n P) = (term201 n P).
Proof. exact (MK_COMB (@lem246912 P n) (@lem246911 n P)). Qed.
Lemma lem246914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246915 (n : nat) (P : nat -> Prop) : (term211 n P) = (term212 n P).
Proof. exact (MK_COMB (@lem246914) (@lem246913 n P)). Qed.
Lemma lem246916 (n : nat) (P : nat -> Prop) (m : nat) : (term208 n P m) = (term185 n P m).
Proof. exact (eq_refl (term208 n P m)). Qed.
Lemma lem246917 (P : nat -> Prop) (n : nat) : (term199 P n) = (term199 P n).
Proof. exact (eq_refl (term199 P n)). Qed.
Lemma lem246918 (n : nat) (P : nat -> Prop) (m : nat) : (term213 n P m) = (term214 n P m).
Proof. exact (MK_COMB (@lem246917 P n) (@lem246916 n P m)). Qed.
Lemma lem246919 (n : nat) (P : nat -> Prop) : (term215 n P) = (term216 n P).
Proof. exact (fun_ext (fun m : nat => @lem246918 n P m)). Qed.
Lemma lem246920 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246921 (n : nat) (P : nat -> Prop) : (term207 n P) = (term217 n P).
Proof. exact (MK_COMB (@lem246920) (@lem246919 n P)). Qed.
Lemma lem246922 (n : nat) (P : nat -> Prop) : ((term206 n P) = (term207 n P)) = ((term201 n P) = (term217 n P)).
Proof. exact (MK_COMB (@lem246915 n P) (@lem246921 n P)). Qed.
Lemma lem246923 (n : nat) (P : nat -> Prop) : (term201 n P) = (term217 n P).
Proof. exact (EQ_MP (@lem246922 n P) (@lem246907 n P)). Qed.
Lemma lem246924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246925 (n : nat) (P : nat -> Prop) : (term203 n P) = (term218 n P).
Proof. exact (MK_COMB (@lem246924) (@lem246923 n P)). Qed.
Lemma lem246926 (n : nat) (P : nat -> Prop) : (term198 n P) = (term198 n P).
Proof. exact (eq_refl (term198 n P)). Qed.
Lemma lem246927 (n : nat) (P : nat -> Prop) : (term205 n P) = (term219 n P).
Proof. exact (MK_COMB (@lem246925 n P) (@lem246926 n P)). Qed.
Lemma lem246929 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem246930 (P : nat -> Prop) (Q : Prop) : (term129 P Q) = (term130 P Q).
Proof. exact (@lem246929 nat P Q). Qed.
Lemma lem246931 (n : nat) (P : nat -> Prop) : (term220 n P) = (term221 n P).
Proof. exact (@lem246930 (term216 n P) (term198 n P)). Qed.
Lemma lem246932 (n : nat) (P : nat -> Prop) (m : nat) : (term222 n P m) = (term214 n P m).
Proof. exact (eq_refl (term222 n P m)). Qed.
Lemma lem246933 (n : nat) (P : nat -> Prop) : (term223 n P) = (term216 n P).
Proof. exact (fun_ext (fun m : nat => @lem246932 n P m)). Qed.
Lemma lem246934 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246935 (n : nat) (P : nat -> Prop) : (term224 n P) = (term217 n P).
Proof. exact (MK_COMB (@lem246934) (@lem246933 n P)). Qed.
Lemma lem246936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246937 (n : nat) (P : nat -> Prop) : (term225 n P) = (term218 n P).
Proof. exact (MK_COMB (@lem246936) (@lem246935 n P)). Qed.
Lemma lem246938 (n : nat) (P : nat -> Prop) : (term198 n P) = (term198 n P).
Proof. exact (eq_refl (term198 n P)). Qed.
Lemma lem246939 (n : nat) (P : nat -> Prop) : (term220 n P) = (term219 n P).
Proof. exact (MK_COMB (@lem246937 n P) (@lem246938 n P)). Qed.
Lemma lem246940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem246941 (n : nat) (P : nat -> Prop) : (term226 n P) = (term227 n P).
Proof. exact (MK_COMB (@lem246940) (@lem246939 n P)). Qed.
Lemma lem246942 (n : nat) (P : nat -> Prop) (m : nat) : (term222 n P m) = (term214 n P m).
Proof. exact (eq_refl (term222 n P m)). Qed.
Lemma lem246943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem246944 (n : nat) (P : nat -> Prop) (m : nat) : (term228 n P m) = (term229 n P m).
Proof. exact (MK_COMB (@lem246943) (@lem246942 n P m)). Qed.
Lemma lem246945 (n : nat) (P : nat -> Prop) : (term198 n P) = (term198 n P).
Proof. exact (eq_refl (term198 n P)). Qed.
Lemma lem246946 (m : nat) (n : nat) (P : nat -> Prop) : (term230 m n P) = (term231 m n P).
Proof. exact (MK_COMB (@lem246944 n P m) (@lem246945 n P)). Qed.
Lemma lem246947 (n : nat) (P : nat -> Prop) : (term232 n P) = (term233 n P).
Proof. exact (fun_ext (fun m : nat => @lem246946 m n P)). Qed.
Lemma lem246948 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem246949 (n : nat) (P : nat -> Prop) : (term221 n P) = (term234 n P).
Proof. exact (MK_COMB (@lem246948) (@lem246947 n P)). Qed.
Lemma lem246950 (n : nat) (P : nat -> Prop) : ((term220 n P) = (term221 n P)) = ((term219 n P) = (term234 n P)).
Proof. exact (MK_COMB (@lem246941 n P) (@lem246949 n P)). Qed.
Lemma lem246951 (n : nat) (P : nat -> Prop) : (term219 n P) = (term234 n P).
Proof. exact (EQ_MP (@lem246950 n P) (@lem246931 n P)). Qed.
Lemma lem246953 (n : nat) (P : nat -> Prop) : (term205 n P) = (term234 n P).
Proof. exact (TRANS (@lem246927 n P) (@lem246951 n P)). Qed.
Lemma lem246954 (n : nat) (P : nat -> Prop) : (term171 n P) = (term234 n P).
Proof. exact (TRANS (@lem246822 n P) (@lem246953 n P)). Qed.
Lemma lem246955 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : term234 n P.
Proof. exact (EQ_MP (@lem246954 n P) (@lem246782 n P h1)). Qed.
Lemma lem246956 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term231 m n P) : term231 m n P.
Proof. exact (h1). Qed.
Lemma lem246969 (n : nat) (P : nat -> Prop) (m : nat) : (term186 n P m) = (term186 n P m).
Proof. exact (eq_refl (term186 n P m)). Qed.
Lemma lem246970 (n : nat) (P : nat -> Prop) : (term194 n P) = (term194 n P).
Proof. exact (fun_ext (fun m : nat => @lem246969 n P m)). Qed.
Lemma lem246971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem246972 (n : nat) (P : nat -> Prop) : (term195 n P) = (term195 n P).
Proof. exact (MK_COMB (@lem246971) (@lem246970 n P)). Qed.
Lemma lem246979 (P : nat -> Prop) (n : nat) : (term196 P n) = (term196 P n).
Proof. exact (eq_refl (term196 P n)). Qed.
Lemma lem246980 (n : nat) (P : nat -> Prop) : (term198 n P) = (term198 n P).
Proof. exact (MK_COMB (@lem246979 P n) (@lem246972 n P)). Qed.
Lemma lem247001 (n : nat) (P : nat -> Prop) (m : nat) : (term229 n P m) = (term229 n P m).
Proof. exact (eq_refl (term229 n P m)). Qed.
Lemma lem247002 (m : nat) (n : nat) (P : nat -> Prop) : (term231 m n P) = (term231 m n P).
Proof. exact (MK_COMB (@lem247001 n P m) (@lem246980 n P)). Qed.
Lemma lem247003 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term231 m n P) : term231 m n P.
Proof. exact (EQ_MP (@lem247002 m n P) (@lem246956 m n P h1)). Qed.
Lemma lem247004 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term214 n P m.
Proof. exact (h1). Qed.
Lemma lem247005 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term198 n P.
Proof. exact (h1). Qed.
Lemma lem247006 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term185 n P m.
Proof. exact (proj2 (@lem247004 n P m h1)). Qed.
Lemma lem247010 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term195 n P.
Proof. exact (proj2 (@lem247005 n P h1)). Qed.
Lemma lem247035 (n : nat) (P : nat -> Prop) (m : nat) : (term186 n P m) = (term186 n P m).
Proof. exact (eq_refl (term186 n P m)). Qed.
Lemma lem247036 (n : nat) (P : nat -> Prop) : (term194 n P) = (term194 n P).
Proof. exact (fun_ext (fun m : nat => @lem247035 n P m)). Qed.
Lemma lem247037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem247039 (n : nat) (P : nat -> Prop) : (term195 n P) = (term195 n P).
Proof. exact (MK_COMB (@lem247037) (@lem247036 n P)). Qed.
Lemma lem247040 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term195 n P.
Proof. exact (EQ_MP (@lem247039 n P) (@lem247010 n P h1)). Qed.
Lemma lem247041 (_4883 : nat) (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term235 n P _4883.
Proof. exact (@lem247040 n P h1 _4883). Qed.
Lemma lem247042 (n : nat) (P : nat -> Prop) (_4883 : nat) : (term235 n P _4883) = (term186 n P _4883).
Proof. exact (eq_refl (term235 n P _4883)). Qed.
Lemma lem247045 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : P n.
Proof. exact (proj1 (@lem247004 n P m h1)). Qed.
Lemma lem247047 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : n = m.
Proof. exact (proj1 (@lem247006 n P m h1)). Qed.
Lemma lem247051 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term147 P n.
Proof. exact (proj1 (@lem247005 n P h1)). Qed.
Lemma lem247057 (_4883 : nat) (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term186 n P _4883.
Proof. exact (EQ_MP (@lem247042 n P _4883) (@lem247041 _4883 n P h1)). Qed.
Lemma lem247072 (P : nat -> Prop) : (term236 P) = (term236 P).
Proof. exact (eq_refl (term236 P)). Qed.
Lemma lem247073 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : (term237 P n) = (term237 P m).
Proof. exact (MK_COMB (@lem247072 P) (@lem247047 n P m h1)). Qed.
Lemma lem247074 (P : nat -> Prop) (m : nat) : (term237 P m) = (P m).
Proof. exact (eq_refl (term237 P m)). Qed.
Lemma lem247075 (P : nat -> Prop) (n : nat) : (term238 P n) = (term238 P n).
Proof. exact (eq_refl (term238 P n)). Qed.
Lemma lem247076 (n : nat) (P : nat -> Prop) (m : nat) : ((term237 P n) = (term237 P m)) = ((term237 P n) = (P m)).
Proof. exact (MK_COMB (@lem247075 P n) (@lem247074 P m)). Qed.
Lemma lem247077 (P : nat -> Prop) (n : nat) : (term237 P n) = (P n).
Proof. exact (eq_refl (term237 P n)). Qed.
Lemma lem247078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem247079 (P : nat -> Prop) (n : nat) : (term238 P n) = (term59 P n).
Proof. exact (MK_COMB (@lem247078) (@lem247077 P n)). Qed.
Lemma lem247080 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem247081 (n : nat) (P : nat -> Prop) (m : nat) : ((term237 P n) = (P m)) = ((P n) = (P m)).
Proof. exact (MK_COMB (@lem247079 P n) (@lem247080 P m)). Qed.
Lemma lem247082 (n : nat) (P : nat -> Prop) (m : nat) : ((term237 P n) = (term237 P m)) = ((P n) = (P m)).
Proof. exact (TRANS (@lem247076 n P m) (@lem247081 n P m)). Qed.
Lemma lem247083 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : (P n) = (P m).
Proof. exact (EQ_MP (@lem247082 n P m) (@lem247073 n P m h1)). Qed.
Lemma lem247098 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term147 P m.
Proof. exact (proj2 (@lem247006 n P m h1)). Qed.
Lemma lem247100 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : P m.
Proof. exact (EQ_MP (@lem247083 n P m h1) (@lem247045 n P m h1)). Qed.
Lemma lem247101 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term239 P m.
Proof. exact (fun h0 : term147 P m => @lem247100 n P m h1). Qed.
Lemma lem247103 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem247104 (P : nat -> Prop) (m : nat) : (term239 P m) = (P m).
Proof. exact (@lem247103 (P m)). Qed.
Lemma lem247105 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : P m.
Proof. exact (EQ_MP (@lem247104 P m) (@lem247101 n P m h1)). Qed.
Lemma lem247108 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem247110 (P : nat -> Prop) (m : nat) : (term147 P m) = (term240 P m).
Proof. exact (@lem247108 (P m)). Qed.
Lemma lem247113 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term240 P m.
Proof. exact (EQ_MP (@lem247110 P m) (@lem247098 n P m h1)). Qed.
Lemma lem247116 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : False.
Proof. exact (@lem247113 n P m h1 (@lem247105 n P m h1)). Qed.
Lemma lem247117 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : term157.
Proof. exact (fun h0 : ~ False => @lem247116 n P m h1). Qed.
Lemma lem247119 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem247120 : term157 = False.
Proof. exact (@lem247119 False). Qed.
Lemma lem247137 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem247138 (n : nat) : n = n.
Proof. exact (@lem247137 n). Qed.
Lemma lem247139 (n : nat) : term241 n.
Proof. exact (fun h0 : term242 n => @lem247138 n). Qed.
Lemma lem247141 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem247142 (n : nat) : (term241 n) = (n = n).
Proof. exact (@lem247141 (n = n)). Qed.
Lemma lem247143 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem247142 n) (@lem247139 n)). Qed.
Lemma lem247149 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem247150 (P : nat -> Prop) (n : nat) (_4883 : nat) : (term186 n P _4883) = (term243 P n _4883).
Proof. exact (@lem247149 (P _4883) (term244 n _4883)). Qed.
Lemma lem247158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem247159 (P : nat -> Prop) (n : nat) (_4883 : nat) : (term245 n P _4883) = (term246 P n _4883).
Proof. exact (MK_COMB (@lem247158) (@lem247150 P n _4883)). Qed.
Lemma lem247167 (P : nat -> Prop) (n : nat) (_4883 : nat) : (term243 P n _4883) = (term243 P n _4883).
Proof. exact (eq_refl (term243 P n _4883)). Qed.
Lemma lem247168 (P : nat -> Prop) (n : nat) (_4883 : nat) : ((term186 n P _4883) = (term243 P n _4883)) = ((term243 P n _4883) = (term243 P n _4883)).
Proof. exact (MK_COMB (@lem247159 P n _4883) (@lem247167 P n _4883)). Qed.
Lemma lem247170 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem247171 (x : Prop) : (x = x) = True.
Proof. exact (@lem247170 Prop x). Qed.
Lemma lem247172 (P : nat -> Prop) (n : nat) (_4883 : nat) : ((term243 P n _4883) = (term243 P n _4883)) = True.
Proof. exact (@lem247171 (term243 P n _4883)). Qed.
Lemma lem247173 (P : nat -> Prop) (n : nat) (_4883 : nat) : ((term186 n P _4883) = (term243 P n _4883)) = True.
Proof. exact (TRANS (@lem247168 P n _4883) (@lem247172 P n _4883)). Qed.
Lemma lem247174 (P : nat -> Prop) (n : nat) (_4883 : nat) : True = ((term186 n P _4883) = (term243 P n _4883)).
Proof. exact (SYM (@lem247173 P n _4883)). Qed.
Lemma lem247175 (P : nat -> Prop) (n : nat) (_4883 : nat) : (term186 n P _4883) = (term243 P n _4883).
Proof. exact (EQ_MP (@lem247174 P n _4883) (@lem0)). Qed.
Lemma lem247176 (_4883 : nat) (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term243 P n _4883.
Proof. exact (EQ_MP (@lem247175 P n _4883) (@lem247057 _4883 n P h1)). Qed.
Lemma lem247178 (b : Prop) (a : Prop) : (a \/ b) = (term164 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem247179 (n : nat) (P : nat -> Prop) (_4883 : nat) : (term243 P n _4883) = (term247 n P _4883).
Proof. exact (@lem247178 (term244 n _4883) (P _4883)). Qed.
Lemma lem247181 (a : Prop) : (term80 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem247182 (n : nat) (_4883 : nat) : (term248 n _4883) = (n = _4883).
Proof. exact (@lem247181 (n = _4883)). Qed.
Lemma lem247183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem247184 (n : nat) (_4883 : nat) : (term249 n _4883) = (term67 n _4883).
Proof. exact (MK_COMB (@lem247183) (@lem247182 n _4883)). Qed.
Lemma lem247185 (P : nat -> Prop) (_4883 : nat) : (P _4883) = (P _4883).
Proof. exact (eq_refl (P _4883)). Qed.
Lemma lem247186 (n : nat) (P : nat -> Prop) (_4883 : nat) : (term247 n P _4883) = (term69 n P _4883).
Proof. exact (MK_COMB (@lem247184 n _4883) (@lem247185 P _4883)). Qed.
Lemma lem247187 (n : nat) (P : nat -> Prop) (_4883 : nat) : (term243 P n _4883) = (term69 n P _4883).
Proof. exact (TRANS (@lem247179 n P _4883) (@lem247186 n P _4883)). Qed.
Lemma lem247190 (_4883 : nat) (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term69 n P _4883.
Proof. exact (EQ_MP (@lem247187 n P _4883) (@lem247176 _4883 n P h1)). Qed.
Lemma lem247191 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term250 P n.
Proof. exact (@lem247190 n n P h1). Qed.
Lemma lem247194 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : P n.
Proof. exact (@lem247191 n P h1 (@lem247143 n)). Qed.
Lemma lem247195 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term239 P n.
Proof. exact (fun h0 : term147 P n => @lem247194 n P h1). Qed.
Lemma lem247197 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem247198 (P : nat -> Prop) (n : nat) : (term239 P n) = (P n).
Proof. exact (@lem247197 (P n)). Qed.
Lemma lem247199 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : P n.
Proof. exact (EQ_MP (@lem247198 P n) (@lem247195 n P h1)). Qed.
Lemma lem247202 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem247204 (P : nat -> Prop) (n : nat) : (term147 P n) = (term240 P n).
Proof. exact (@lem247202 (P n)). Qed.
Lemma lem247207 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term240 P n.
Proof. exact (EQ_MP (@lem247204 P n) (@lem247051 n P h1)). Qed.
Lemma lem247210 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : False.
Proof. exact (@lem247207 n P h1 (@lem247199 n P h1)). Qed.
Lemma lem247211 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : term157.
Proof. exact (fun h0 : ~ False => @lem247210 n P h1). Qed.
Lemma lem247213 (p : Prop) : (term155 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem247214 : term157 = False.
Proof. exact (@lem247213 False). Qed.
Lemma lem247215 (n : nat) (P : nat -> Prop) (h1 : term198 n P) : False.
Proof. exact (EQ_MP (@lem247214) (@lem247211 n P h1)). Qed.
Lemma lem247216 (n : nat) (P : nat -> Prop) (m : nat) (h1 : term214 n P m) : False.
Proof. exact (EQ_MP (@lem247120) (@lem247117 n P m h1)). Qed.
Lemma lem247217 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term231 m n P) : False.
Proof. exact (or_elim (@lem247003 m n P h1) (fun h0 : term214 n P m => @lem247216 n P m h0) (fun h0 : term198 n P => @lem247215 n P h0)). Qed.
Lemma lem247218 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term231 m n P) : (term231 m n P) = False.
Proof. exact (prop_ext (fun h2 : term231 m n P => @lem247217 m n P h1) (fun h2 : False => @lem247003 m n P h1)). Qed.
Lemma lem247219 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term231 m n P) : False.
Proof. exact (EQ_MP (@lem247218 m n P h1) (@lem247003 m n P h1)). Qed.
Lemma lem247220 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : False.
Proof. exact (ex_elim (@lem246955 n P h1) (fun m : nat => fun h0 : term233 n P m => @lem247219 m n P h0)). Qed.
Lemma lem247221 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : (term171 n P) = False.
Proof. exact (prop_ext (fun h2 : term171 n P => @lem247220 n P h1) (fun h2 : False => @lem246782 n P h1)). Qed.
Lemma lem247222 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : False.
Proof. exact (EQ_MP (@lem247221 n P h1) (@lem246782 n P h1)). Qed.
Lemma lem247223 (n : nat) (P : nat -> Prop) : term170 n P.
Proof. exact (fun h0 : term171 n P => @lem247222 n P h0). Qed.
Lemma lem247224 (n : nat) (P : nat -> Prop) : (P n) = (term72 n P).
Proof. exact (EQ_MP (@lem246781 n P) (@lem247223 n P)). Qed.
Lemma lem247229 (P : nat -> Prop) : term179 P.
Proof. exact (fun n : nat => @lem247224 n P). Qed.
Lemma lem247234 : term183.
Proof. exact (fun P : nat -> Prop => @lem247229 P). Qed.
Lemma lem247235 : term182.
Proof. exact (EQ_MP (@lem246777) (@lem247234)). Qed.
Lemma lem247236 (P : nat -> Prop) : term251 P.
Proof. exact (@lem247235 P). Qed.
Lemma lem247237 (P : nat -> Prop) : (term251 P) = (term178 P).
Proof. exact (eq_refl (term251 P)). Qed.
Lemma lem247238 (P : nat -> Prop) : term178 P.
Proof. exact (EQ_MP (@lem247237 P) (@lem247236 P)). Qed.
Lemma lem247239 (P : nat -> Prop) (n : nat) : term252 P n.
Proof. exact (@lem247238 P n). Qed.
Lemma lem247240 (n : nat) (P : nat -> Prop) : (term252 P n) = (term170 n P).
Proof. exact (eq_refl (term252 P n)). Qed.
Lemma lem247241 (n : nat) (P : nat -> Prop) : term170 n P.
Proof. exact (EQ_MP (@lem247240 n P) (@lem247239 P n)). Qed.
Lemma lem247243 (n : nat) (P : nat -> Prop) : term170 n P.
Proof. exact (@lem246696 n P (@lem247241 n P)). Qed.
Lemma lem247244 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : False.
Proof. exact (@lem247243 n P (@lem246681 n P h1)). Qed.
Lemma lem247245 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : (term171 n P) = False.
Proof. exact (prop_ext (fun h2 : term171 n P => @lem247244 n P h1) (fun h2 : False => @lem246681 n P h1)). Qed.
Lemma lem247246 (n : nat) (P : nat -> Prop) (h1 : term171 n P) : False.
Proof. exact (EQ_MP (@lem247245 n P h1) (@lem246681 n P h1)). Qed.
Lemma lem247247 (n : nat) (P : nat -> Prop) : term170 n P.
Proof. exact (fun h0 : term171 n P => @lem247246 n P h0). Qed.
Lemma lem247248 (n : nat) (P : nat -> Prop) : (P n) = (term72 n P).
Proof. exact (EQ_MP (@lem246680 n P) (@lem247247 n P)). Qed.
Lemma lem247249 (n : nat) (P : nat -> Prop) : (term25 P n) = (term26 n P).
Proof. exact (EQ_MP (@lem246116 n P) (@lem247248 n P)). Qed.
Lemma lem247250 (P : nat -> Prop) : (term15 P) = (term16 P).
Proof. exact (EQ_MP (@lem246055 P) (@lem246676 P)). Qed.
Lemma lem247251 (n : nat) (P : nat -> Prop) : term28 n P.
Proof. exact (fun h0 : (term20 P n) = (term21 n P) => @lem247249 n P). Qed.
Lemma lem247256 (P : nat -> Prop) : term32 P.
Proof. exact (fun n : nat => @lem247251 n P). Qed.
Lemma lem247257 (P : nat -> Prop) : term34 P.
Proof. exact (conj (@lem247250 P) (@lem247256 P)). Qed.
Lemma lem247258 (P : nat -> Prop) : term39 P.
Proof. exact (@lem245991 P (@lem247257 P)). Qed.
Lemma lem247259 (P : nat -> Prop) (n : nat) : term19 P n.
Proof. exact (@lem247258 P n). Qed.
Lemma lem247260 (n : nat) (P : nat -> Prop) : (term19 P n) = ((term20 P n) = (term21 n P)).
Proof. exact (eq_refl (term19 P n)). Qed.
Lemma lem247261 (n : nat) (P : nat -> Prop) : (term20 P n) = (term21 n P).
Proof. exact (EQ_MP (@lem247260 n P) (@lem247259 P n)). Qed.
