Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ANTISYM_term_abbrevs.
Require Import LE_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem92041 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem92042 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem92041 n h1)). Qed.
Lemma lem92043 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem92044 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem92043 n h1)). Qed.
Lemma lem92045 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem92042 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem92044 n h1)). Qed.
Lemma lem92046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92047 (n : nat) : (term0 n) = (term1 n).
Proof. exact (MK_COMB (@lem92046) (@lem92045 n)). Qed.
Lemma lem92048 : term2 = term3.
Proof. exact (fun_ext (fun n : nat => @lem92047 n)). Qed.
Lemma lem92049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92050 : term4 = term5.
Proof. exact (MK_COMB (@lem92049) (@lem92048)). Qed.
Lemma lem92051 : term5.
Proof. exact (EQ_MP (@lem92050) (@lem75570)). Qed.
Lemma lem92052 (n : nat) : term6 n.
Proof. exact (@lem92051 n). Qed.
Lemma lem92053 (n : nat) : (term6 n) = (term1 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem92054 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem92053 n) (@lem92052 n)). Qed.
Lemma lem92055 (n : nat) : term7 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem92058 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem92059 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem92058 n h1)). Qed.
Lemma lem92060 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem92061 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem92060 n h1)). Qed.
Lemma lem92062 (n : nat) : ((NUMERAL 0) = (S n)) = ((S n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (S n) => @lem92059 n h1) (fun h1 : (S n) = (NUMERAL 0) => @lem92061 n h1)). Qed.
Lemma lem92063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92064 (n : nat) : (term1 n) = (term0 n).
Proof. exact (MK_COMB (@lem92063) (@lem92062 n)). Qed.
Lemma lem92065 (n : nat) : term0 n.
Proof. exact (EQ_MP (@lem92064 n) (@lem92054 n)). Qed.
Lemma lem92066 (n : nat) : term8 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem92084 : term9.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem92085 (m : nat) : term10 m.
Proof. exact (@lem92084 m). Qed.
Lemma lem92086 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem92087 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem92086 m) (@lem92085 m)). Qed.
Lemma lem92088 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem92087 m n). Qed.
Lemma lem92089 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem92091 : term15.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem92092 (m : nat) : term16 m.
Proof. exact (@lem92091 m). Qed.
Lemma lem92093 (m : nat) : (term16 m) = ((term17 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem92096 (P : nat -> Prop) : term18 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92097 : term19.
Proof. exact (@lem92096 term20). Qed.
Lemma lem92098 : term21 = term22.
Proof. exact (eq_refl term21). Qed.
Lemma lem92099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92100 : term23 = term24.
Proof. exact (MK_COMB (@lem92099) (@lem92098)). Qed.
Lemma lem92101 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem92102 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92103 (m : nat) : (term27 m) = (term28 m).
Proof. exact (MK_COMB (@lem92102) (@lem92101 m)). Qed.
Lemma lem92104 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem92105 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem92103 m) (@lem92104 m)). Qed.
Lemma lem92106 : term33 = term34.
Proof. exact (fun_ext (fun m : nat => @lem92105 m)). Qed.
Lemma lem92107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92108 : term35 = term36.
Proof. exact (MK_COMB (@lem92107) (@lem92106)). Qed.
Lemma lem92109 : term37 = term38.
Proof. exact (MK_COMB (@lem92100) (@lem92108)). Qed.
Lemma lem92110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92111 : term39 = term40.
Proof. exact (MK_COMB (@lem92110) (@lem92109)). Qed.
Lemma lem92112 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem92113 : term41 = term20.
Proof. exact (fun_ext (fun m : nat => @lem92112 m)). Qed.
Lemma lem92114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92115 : term42 = term43.
Proof. exact (MK_COMB (@lem92114) (@lem92113)). Qed.
Lemma lem92116 : term19 = term44.
Proof. exact (MK_COMB (@lem92111) (@lem92115)). Qed.
Lemma lem92117 : term44.
Proof. exact (EQ_MP (@lem92116) (@lem92097)). Qed.
Lemma lem92118 (m : nat) (h1 : term26 m) : term26 m.
Proof. exact (h1). Qed.
Lemma lem92120 (P : nat -> Prop) : term18 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92121 : term45.
Proof. exact (@lem92120 term46). Qed.
Lemma lem92122 : term47 = (term48 = ((NUMERAL 0) = (NUMERAL 0))).
Proof. exact (eq_refl term47). Qed.
Lemma lem92123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92124 : term49 = term50.
Proof. exact (MK_COMB (@lem92123) (@lem92122)). Qed.
Lemma lem92125 (n : nat) : (term51 n) = ((term52 n) = ((NUMERAL 0) = n)).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem92126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92127 (n : nat) : (term53 n) = (term54 n).
Proof. exact (MK_COMB (@lem92126) (@lem92125 n)). Qed.
Lemma lem92128 (n : nat) : (term55 n) = ((term56 n) = ((NUMERAL 0) = (S n))).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem92129 (n : nat) : (term57 n) = (term58 n).
Proof. exact (MK_COMB (@lem92127 n) (@lem92128 n)). Qed.
Lemma lem92130 : term59 = term60.
Proof. exact (fun_ext (fun n : nat => @lem92129 n)). Qed.
Lemma lem92131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92132 : term61 = term62.
Proof. exact (MK_COMB (@lem92131) (@lem92130)). Qed.
Lemma lem92133 : term63 = term64.
Proof. exact (MK_COMB (@lem92124) (@lem92132)). Qed.
Lemma lem92134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92135 : term65 = term66.
Proof. exact (MK_COMB (@lem92134) (@lem92133)). Qed.
Lemma lem92136 (n : nat) : (term51 n) = ((term52 n) = ((NUMERAL 0) = n)).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem92137 : term67 = term46.
Proof. exact (fun_ext (fun n : nat => @lem92136 n)). Qed.
Lemma lem92138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92139 : term68 = term22.
Proof. exact (MK_COMB (@lem92138) (@lem92137)). Qed.
Lemma lem92140 : term45 = term69.
Proof. exact (MK_COMB (@lem92135) (@lem92139)). Qed.
Lemma lem92141 : term69.
Proof. exact (EQ_MP (@lem92140) (@lem92121)). Qed.
Lemma lem92148 (P : nat -> Prop) : term18 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92149 (m : nat) : term70 m.
Proof. exact (@lem92148 (term71 m)). Qed.
Lemma lem92150 (m : nat) : (term72 m) = ((term73 m) = ((S m) = (NUMERAL 0))).
Proof. exact (eq_refl (term72 m)). Qed.
Lemma lem92151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92152 (m : nat) : (term74 m) = (term75 m).
Proof. exact (MK_COMB (@lem92151) (@lem92150 m)). Qed.
Lemma lem92153 (m : nat) (n : nat) : (term76 m n) = ((term77 n m) = ((S m) = n)).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem92154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92155 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem92154) (@lem92153 m n)). Qed.
Lemma lem92156 (m : nat) (n : nat) : (term80 m n) = ((term81 n m) = ((S m) = (S n))).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem92157 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem92155 m n) (@lem92156 m n)). Qed.
Lemma lem92158 (m : nat) : (term84 m) = (term85 m).
Proof. exact (fun_ext (fun n : nat => @lem92157 m n)). Qed.
Lemma lem92159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92160 (m : nat) : (term86 m) = (term87 m).
Proof. exact (MK_COMB (@lem92159) (@lem92158 m)). Qed.
Lemma lem92161 (m : nat) : (term88 m) = (term89 m).
Proof. exact (MK_COMB (@lem92152 m) (@lem92160 m)). Qed.
Lemma lem92162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92163 (m : nat) : (term90 m) = (term91 m).
Proof. exact (MK_COMB (@lem92162) (@lem92161 m)). Qed.
Lemma lem92164 (m : nat) (n : nat) : (term76 m n) = ((term77 n m) = ((S m) = n)).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem92165 (m : nat) : (term92 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem92164 m n)). Qed.
Lemma lem92166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92167 (m : nat) : (term93 m) = (term30 m).
Proof. exact (MK_COMB (@lem92166) (@lem92165 m)). Qed.
Lemma lem92168 (m : nat) : (term70 m) = (term94 m).
Proof. exact (MK_COMB (@lem92163 m) (@lem92167 m)). Qed.
Lemma lem92169 (m : nat) : term94 m.
Proof. exact (EQ_MP (@lem92168 m) (@lem92149 m)). Qed.
Lemma lem92190 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem92191 : term48 = term95.
Proof. exact (@lem92190 term95). Qed.
Lemma lem92192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem92193 : term96 = term97.
Proof. exact (MK_COMB (@lem92192) (@lem92191)). Qed.
Lemma lem92195 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem92196 (x : nat) : (x = x) = True.
Proof. exact (@lem92195 nat x). Qed.
Lemma lem92197 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem92196 (NUMERAL 0)). Qed.
Lemma lem92198 : (term48 = ((NUMERAL 0) = (NUMERAL 0))) = (term95 = True).
Proof. exact (MK_COMB (@lem92193) (@lem92197)). Qed.
Lemma lem92200 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem92201 : (term95 = True) = term95.
Proof. exact (@lem92200 term95). Qed.
Lemma lem92202 : (term48 = ((NUMERAL 0) = (NUMERAL 0))) = term95.
Proof. exact (TRANS (@lem92198) (@lem92201)). Qed.
Lemma lem92203 : term95 = (term48 = ((NUMERAL 0) = (NUMERAL 0))).
Proof. exact (SYM (@lem92202)). Qed.
Lemma lem92247 (m : nat) : term98 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem92248 (m : nat) : (term98 m) = (term99 m).
Proof. exact (eq_refl (term98 m)). Qed.
Lemma lem92249 (m : nat) : term99 m.
Proof. exact (EQ_MP (@lem92248 m) (@lem92247 m)). Qed.
Lemma lem92250 (m : nat) (n : nat) : term100 m n.
Proof. exact (@lem92249 m n). Qed.
Lemma lem92251 (m : nat) (n : nat) : (term100 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term100 m n)). Qed.
Lemma lem92253 (m : nat) : term101 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem92254 (m : nat) : (term101 m) = (term102 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem92255 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem92254 m) (@lem92253 m)). Qed.
Lemma lem92256 (m : nat) (n : nat) : term103 m n.
Proof. exact (@lem92255 m n). Qed.
Lemma lem92257 (m : nat) (n : nat) : (term103 m n) = ((term104 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term103 m n)). Qed.
Lemma lem92259 (n : nat) (m : nat) (h1 : term26 m) : term105 m n.
Proof. exact (@lem92118 m h1 n). Qed.
Lemma lem92260 (m : nat) (n : nat) : (term105 m n) = ((term106 n m) = (m = n)).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem92267 (m : nat) (n : nat) : (term104 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem92257 m n) (@lem92256 m n)). Qed.
Lemma lem92268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92269 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem92268) (@lem92267 m n)). Qed.
Lemma lem92271 (m : nat) (n : nat) : (term104 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem92257 m n) (@lem92256 m n)). Qed.
Lemma lem92272 (n : nat) (m : nat) : (term104 n m) = (Peano.le n m).
Proof. exact (@lem92271 n m). Qed.
Lemma lem92273 (n : nat) (m : nat) : (term81 n m) = (term106 n m).
Proof. exact (MK_COMB (@lem92269 m n) (@lem92272 n m)). Qed.
Lemma lem92275 (n : nat) (m : nat) (h1 : term26 m) : (term106 n m) = (m = n).
Proof. exact (EQ_MP (@lem92260 m n) (@lem92259 n m h1)). Qed.
Lemma lem92278 (n : nat) (m : nat) (h1 : term26 m) : (term81 n m) = (m = n).
Proof. exact (TRANS (@lem92273 n m) (@lem92275 n m h1)). Qed.
Lemma lem92279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem92280 (n : nat) (m : nat) (h1 : term26 m) : (term109 n m) = (term110 m n).
Proof. exact (MK_COMB (@lem92279) (@lem92278 n m h1)). Qed.
Lemma lem92282 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem92251 m n) (@lem92250 m n)). Qed.
Lemma lem92285 (n : nat) (m : nat) (h1 : term26 m) : ((term81 n m) = ((S m) = (S n))) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem92280 n m h1) (@lem92282 m n)). Qed.
Lemma lem92287 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem92288 (x : Prop) : (x = x) = True.
Proof. exact (@lem92287 Prop x). Qed.
Lemma lem92289 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem92288 (m = n)). Qed.
Lemma lem92290 (n : nat) (m : nat) (h1 : term26 m) : ((term81 n m) = ((S m) = (S n))) = True.
Proof. exact (TRANS (@lem92285 n m h1) (@lem92289 m n)). Qed.
Lemma lem92291 (n : nat) (m : nat) (h1 : term26 m) : True = ((term81 n m) = ((S m) = (S n))).
Proof. exact (SYM (@lem92290 n m h1)). Qed.
Lemma lem92292 (n : nat) (m : nat) (h1 : term26 m) : (term81 n m) = ((S m) = (S n)).
Proof. exact (EQ_MP (@lem92291 n m h1) (@lem0)). Qed.
Lemma lem92294 (m : nat) : (term17 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92093 m) (@lem92092 m)). Qed.
Lemma lem92295 : term95 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem92294 (NUMERAL 0)). Qed.
Lemma lem92297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem92298 (x : nat) : (x = x) = True.
Proof. exact (@lem92297 nat x). Qed.
Lemma lem92299 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem92298 (NUMERAL 0)). Qed.
Lemma lem92300 : term95 = True.
Proof. exact (TRANS (@lem92295) (@lem92299)). Qed.
Lemma lem92301 : True = term95.
Proof. exact (SYM (@lem92300)). Qed.
Lemma lem92302 : term95.
Proof. exact (EQ_MP (@lem92301) (@lem0)). Qed.
Lemma lem92308 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem92089 m n) (@lem92088 m n)). Qed.
Lemma lem92309 (n : nat) : (term111 n) = (term112 n).
Proof. exact (@lem92308 (NUMERAL 0) n). Qed.
Lemma lem92313 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem92055 n (@lem92054 n)). Qed.
Lemma lem92314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem92315 (n : nat) : (term113 n) = (or False).
Proof. exact (MK_COMB (@lem92314) (@lem92313 n)). Qed.
Lemma lem92316 (n : nat) : (term114 n) = (term114 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem92317 (n : nat) : (term112 n) = (term115 n).
Proof. exact (MK_COMB (@lem92315 n) (@lem92316 n)). Qed.
Lemma lem92319 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem92320 (n : nat) : (term115 n) = (term114 n).
Proof. exact (@lem92319 (term114 n)). Qed.
Lemma lem92321 (n : nat) : (term112 n) = (term114 n).
Proof. exact (TRANS (@lem92317 n) (@lem92320 n)). Qed.
Lemma lem92322 (n : nat) : (term111 n) = (term114 n).
Proof. exact (TRANS (@lem92309 n) (@lem92321 n)). Qed.
Lemma lem92323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92324 (n : nat) : (term116 n) = (term117 n).
Proof. exact (MK_COMB (@lem92323) (@lem92322 n)). Qed.
Lemma lem92326 (m : nat) : (term17 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92093 m) (@lem92092 m)). Qed.
Lemma lem92327 (n : nat) : (term118 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem92326 (S n)). Qed.
Lemma lem92329 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem92066 n (@lem92065 n)). Qed.
Lemma lem92330 (n : nat) : (term118 n) = False.
Proof. exact (TRANS (@lem92327 n) (@lem92329 n)). Qed.
Lemma lem92331 (n : nat) : (term56 n) = (term119 n).
Proof. exact (MK_COMB (@lem92324 n) (@lem92330 n)). Qed.
Lemma lem92333 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem92334 (n : nat) : (term119 n) = False.
Proof. exact (@lem92333 (term114 n)). Qed.
Lemma lem92335 (n : nat) : (term56 n) = False.
Proof. exact (TRANS (@lem92331 n) (@lem92334 n)). Qed.
Lemma lem92336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem92337 (n : nat) : (term120 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem92336) (@lem92335 n)). Qed.
Lemma lem92339 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem92055 n (@lem92054 n)). Qed.
Lemma lem92340 (n : nat) : ((term56 n) = ((NUMERAL 0) = (S n))) = (False = False).
Proof. exact (MK_COMB (@lem92337 n) (@lem92339 n)). Qed.
Lemma lem92342 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem92343 : (False = False) = (~ False).
Proof. exact (@lem92342 False). Qed.
Lemma lem92345 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92346 : (False = False) = True.
Proof. exact (TRANS (@lem92343) (@lem92345)). Qed.
Lemma lem92347 (n : nat) : ((term56 n) = ((NUMERAL 0) = (S n))) = True.
Proof. exact (TRANS (@lem92340 n) (@lem92346)). Qed.
Lemma lem92348 (n : nat) : True = ((term56 n) = ((NUMERAL 0) = (S n))).
Proof. exact (SYM (@lem92347 n)). Qed.
Lemma lem92355 (m : nat) : (term17 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92093 m) (@lem92092 m)). Qed.
Lemma lem92356 (m : nat) : (term118 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem92355 (S m)). Qed.
Lemma lem92358 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem92066 n (@lem92065 n)). Qed.
Lemma lem92359 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem92358 m). Qed.
Lemma lem92360 (m : nat) : (term118 m) = False.
Proof. exact (TRANS (@lem92356 m) (@lem92359 m)). Qed.
Lemma lem92361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92362 (m : nat) : (term121 m) = (and False).
Proof. exact (MK_COMB (@lem92361) (@lem92360 m)). Qed.
Lemma lem92364 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem92089 m n) (@lem92088 m n)). Qed.
Lemma lem92365 (m : nat) : (term111 m) = (term112 m).
Proof. exact (@lem92364 (NUMERAL 0) m). Qed.
Lemma lem92369 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem92055 n (@lem92054 n)). Qed.
Lemma lem92370 (m : nat) : ((NUMERAL 0) = (S m)) = False.
Proof. exact (@lem92369 m). Qed.
Lemma lem92371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem92372 (m : nat) : (term113 m) = (or False).
Proof. exact (MK_COMB (@lem92371) (@lem92370 m)). Qed.
Lemma lem92373 (m : nat) : (term114 m) = (term114 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem92374 (m : nat) : (term112 m) = (term115 m).
Proof. exact (MK_COMB (@lem92372 m) (@lem92373 m)). Qed.
Lemma lem92376 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem92377 (m : nat) : (term115 m) = (term114 m).
Proof. exact (@lem92376 (term114 m)). Qed.
Lemma lem92378 (m : nat) : (term112 m) = (term114 m).
Proof. exact (TRANS (@lem92374 m) (@lem92377 m)). Qed.
Lemma lem92379 (m : nat) : (term111 m) = (term114 m).
Proof. exact (TRANS (@lem92365 m) (@lem92378 m)). Qed.
Lemma lem92380 (m : nat) : (term73 m) = (term122 m).
Proof. exact (MK_COMB (@lem92362 m) (@lem92379 m)). Qed.
Lemma lem92382 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem92383 (m : nat) : (term122 m) = False.
Proof. exact (@lem92382 (term114 m)). Qed.
Lemma lem92384 (m : nat) : (term73 m) = False.
Proof. exact (TRANS (@lem92380 m) (@lem92383 m)). Qed.
Lemma lem92385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem92386 (m : nat) : (term123 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem92385) (@lem92384 m)). Qed.
Lemma lem92388 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem92066 n (@lem92065 n)). Qed.
Lemma lem92389 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem92388 m). Qed.
Lemma lem92390 (m : nat) : ((term73 m) = ((S m) = (NUMERAL 0))) = (False = False).
Proof. exact (MK_COMB (@lem92386 m) (@lem92389 m)). Qed.
Lemma lem92392 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem92393 : (False = False) = (~ False).
Proof. exact (@lem92392 False). Qed.
Lemma lem92395 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92396 : (False = False) = True.
Proof. exact (TRANS (@lem92393) (@lem92395)). Qed.
Lemma lem92397 (m : nat) : ((term73 m) = ((S m) = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem92390 m) (@lem92396)). Qed.
Lemma lem92398 (m : nat) : True = ((term73 m) = ((S m) = (NUMERAL 0))).
Proof. exact (SYM (@lem92397 m)). Qed.
Lemma lem92400 (m : nat) : (term73 m) = ((S m) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92398 m) (@lem0)). Qed.
Lemma lem92401 (n : nat) : (term56 n) = ((NUMERAL 0) = (S n)).
Proof. exact (EQ_MP (@lem92348 n) (@lem0)). Qed.
Lemma lem92402 : term48 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92203) (@lem92302)). Qed.
Lemma lem92403 (n : nat) (m : nat) (h1 : term26 m) : term83 m n.
Proof. exact (fun h0 : (term77 n m) = ((S m) = n) => @lem92292 n m h1). Qed.
Lemma lem92408 (m : nat) (h1 : term26 m) : term87 m.
Proof. exact (fun n : nat => @lem92403 n m h1). Qed.
Lemma lem92409 (m : nat) (h1 : term26 m) : term89 m.
Proof. exact (conj (@lem92400 m) (@lem92408 m h1)). Qed.
Lemma lem92410 (m : nat) (h1 : term26 m) : term30 m.
Proof. exact (@lem92169 m (@lem92409 m h1)). Qed.
Lemma lem92411 (n : nat) : term58 n.
Proof. exact (fun h0 : (term52 n) = ((NUMERAL 0) = n) => @lem92401 n). Qed.
Lemma lem92416 : term62.
Proof. exact (fun n : nat => @lem92411 n). Qed.
Lemma lem92417 : term64.
Proof. exact (conj (@lem92402) (@lem92416)). Qed.
Lemma lem92418 : term22.
Proof. exact (@lem92141 (@lem92417)). Qed.
Lemma lem92419 (m : nat) : term32 m.
Proof. exact (fun h0 : term26 m => @lem92410 m h0). Qed.
Lemma lem92424 : term36.
Proof. exact (fun m : nat => @lem92419 m). Qed.
Lemma lem92425 : term38.
Proof. exact (conj (@lem92418) (@lem92424)). Qed.
Lemma lem92426 : term43.
Proof. exact (@lem92117 (@lem92425)). Qed.
