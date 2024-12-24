Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_term_abbrevs.
Require Import FINITE_SUBSET_spec.
Require Import FINITE_UNION_IMP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm1842_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem3606102 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3606103 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3606102 A h1 s). Qed.
Lemma lem3606104 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3606105 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3606104 A s) (@lem3606103 A s h1)). Qed.
Lemma lem3606106 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3606105 A s h1 t). Qed.
Lemma lem3606107 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3606108 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3606107 A t s) (@lem3606106 A s t h1)). Qed.
Lemma lem3606109 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3606110 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3606108 A t s h1 (@lem3606109 A s t h2)). Qed.
Lemma lem3606111 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3606110 A s t h0 h1). Qed.
Lemma lem3606112 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3606113 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3606112 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3606111 A s t h0)). Qed.
Lemma lem3606114 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3606115 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3606113 A s h2 (@lem3606114 A h1)). Qed.
Lemma lem3606116 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3606115 A s h1 h0). Qed.
Lemma lem3606117 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3606116 A s h1). Qed.
Lemma lem3606118 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3606117 A h0). Qed.
Lemma lem3606119 {A : Type'} : term10 A.
Proof. exact (@lem3606118 A (@lem3599924 A)). Qed.
Lemma lem3606120 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3606119 A s). Qed.
Lemma lem3606121 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3606123 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term13 A s t.
Proof. exact (h1). Qed.
Lemma lem3606125 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3606121 A s) (@lem3606120 A s)). Qed.
Lemma lem3606126 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3606125 A s). Qed.
Lemma lem3606128 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3606121 A s) (@lem3606120 A s)). Qed.
Lemma lem3606129 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3606128 A s). Qed.
Lemma lem3606130 {A : Type'} (t : A -> Prop) : term9 A t.
Proof. exact (@lem3606129 A t). Qed.
Lemma lem3606131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((term13 A s t) = True).
Proof. exact (@lem7 (term13 A s t)). Qed.
Lemma lem3606136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term13 A s t) = True.
Proof. exact (EQ_MP (@lem3606131 A s t) (@lem3606123 A s t h1)). Qed.
Lemma lem3606137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3606138 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term14 A s t) = (and True).
Proof. exact (MK_COMB (@lem3606137) (@lem3606136 A s t h1)). Qed.
Lemma lem3606139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term15 A s t).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem3606140 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term16 A s t) = (term17 A s t).
Proof. exact (MK_COMB (@lem3606138 A s t h1) (@lem3606139 A s t)). Qed.
Lemma lem3606142 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3606143 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term15 A s t).
Proof. exact (@lem3606142 (term15 A s t)). Qed.
Lemma lem3606144 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term16 A s t) = (term15 A s t).
Proof. exact (TRANS (@lem3606140 A s t h1) (@lem3606143 A s t)). Qed.
Lemma lem3606145 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term15 A s t) = (term16 A s t).
Proof. exact (SYM (@lem3606144 A s t h1)). Qed.
Lemma lem3606146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((term13 A s t) = True).
Proof. exact (@lem7 (term13 A s t)). Qed.
Lemma lem3606151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term13 A s t) = True.
Proof. exact (EQ_MP (@lem3606146 A s t) (@lem3606123 A s t h1)). Qed.
Lemma lem3606152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3606153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term14 A s t) = (and True).
Proof. exact (MK_COMB (@lem3606152) (@lem3606151 A s t h1)). Qed.
Lemma lem3606154 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term18 A s t).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem3606155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term19 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3606153 A s t h1) (@lem3606154 A s t)). Qed.
Lemma lem3606157 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3606158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term18 A s t).
Proof. exact (@lem3606157 (term18 A s t)). Qed.
Lemma lem3606159 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term19 A s t) = (term18 A s t).
Proof. exact (TRANS (@lem3606155 A s t h1) (@lem3606158 A s t)). Qed.
Lemma lem3606160 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term18 A s t) = (term19 A s t).
Proof. exact (SYM (@lem3606159 A s t h1)). Qed.
Lemma lem3606162 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3606163 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (@lem3606162 A s t). Qed.
Lemma lem3606164 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term22 A s t).
Proof. exact (@lem3606163 A s (@UNION A s t)). Qed.
Lemma lem3606171 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term15 A s t).
Proof. exact (SYM (@lem3606164 A s t)). Qed.
Lemma lem3606179 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606180 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606179 A P x). Qed.
Lemma lem3606181 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3606180 A s x). Qed.
Lemma lem3606182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3606183 {A : Type'} (s : A -> Prop) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (MK_COMB (@lem3606182) (@lem3606181 A s x)). Qed.
Lemma lem3606185 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3606186 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3606185 A s x t). Qed.
Lemma lem3606190 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606191 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606190 A P x). Qed.
Lemma lem3606192 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3606191 A s x). Qed.
Lemma lem3606193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3606194 {A : Type'} (s : A -> Prop) (x : A) : (term27 A x s) = (term28 A s x).
Proof. exact (MK_COMB (@lem3606193) (@lem3606192 A s x)). Qed.
Lemma lem3606196 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606196 A P x). Qed.
Lemma lem3606198 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3606197 A t x). Qed.
Lemma lem3606199 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term26 A s x t) = (term29 A s t x).
Proof. exact (MK_COMB (@lem3606194 A s x) (@lem3606198 A t x)). Qed.
Lemma lem3606202 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term25 A x s t) = (term29 A s t x).
Proof. exact (TRANS (@lem3606186 A s x t) (@lem3606199 A s t x)). Qed.
Lemma lem3606203 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A x s t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3606183 A s x) (@lem3606202 A s t x)). Qed.
Lemma lem3606206 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3606203 A s t x)). Qed.
Lemma lem3606207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3606208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3606207 A) (@lem3606206 A s t)). Qed.
Lemma lem3606213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term22 A s t).
Proof. exact (SYM (@lem3606208 A s t)). Qed.
Lemma lem3606215 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3606216 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term36 A s t).
Proof. exact (@lem3606215 (term34 A s t)). Qed.
Lemma lem3606217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term34 A s t).
Proof. exact (SYM (@lem3606216 A s t)). Qed.
Lemma lem3606218 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A s t) : term37 A s t.
Proof. exact (h1). Qed.
Lemma lem3606221 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term36 A s t) : term36 A s t.
Proof. exact (h1). Qed.
Lemma lem3606222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term38 A s t.
Proof. exact (fun h0 : term36 A s t => @lem3606221 A s t h0). Qed.
Lemma lem3606223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term38 A s t) : term38 A s t.
Proof. exact (h1). Qed.
Lemma lem3606224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term36 A s t) : term36 A s t.
Proof. exact (h1). Qed.
Lemma lem3606225 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term36 A s t) (h2 : term38 A s t) : term36 A s t.
Proof. exact (@lem3606223 A s t h2 (@lem3606224 A s t h1)). Qed.
Lemma lem3606226 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term36 A s t) : term39 A s t.
Proof. exact (fun h0 : term38 A s t => @lem3606225 A s t h1 h0). Qed.
Lemma lem3606227 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term38 A s t) : term38 A s t.
Proof. exact (h1). Qed.
Lemma lem3606228 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term36 A s t) (h2 : term38 A s t) : term36 A s t.
Proof. exact (@lem3606226 A s t h1 (@lem3606227 A s t h2)). Qed.
Lemma lem3606229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term38 A s t) : term38 A s t.
Proof. exact (fun h0 : term36 A s t => @lem3606228 A s t h0 h1). Qed.
Lemma lem3606230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term40 A s t.
Proof. exact (fun h0 : term38 A s t => @lem3606229 A s t h0). Qed.
Lemma lem3606233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term38 A s t.
Proof. exact (@lem3606230 A s t (@lem3606222 A s t)). Qed.
Lemma lem3606234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term38 A s t.
Proof. exact (@lem3606233 A s t). Qed.
Lemma lem3606244 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3606245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term41 A s t).
Proof. exact (@lem3606244 (term37 A s t)). Qed.
Lemma lem3606247 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3606248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term34 A s t).
Proof. exact (@lem3606247 (term34 A s t)). Qed.
Lemma lem3606253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term34 A s t).
Proof. exact (TRANS (@lem3606245 A s t) (@lem3606248 A s t)). Qed.
Lemma lem3606258 {A : Type'} (t : A -> Prop) : (term43 A t) = (term44 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606253 A s t)). Qed.
Lemma lem3606259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606260 {A : Type'} (t : A -> Prop) : (term45 A t) = (term46 A t).
Proof. exact (MK_COMB (@lem3606259 A) (@lem3606258 A t)). Qed.
Lemma lem3606265 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606260 A t)). Qed.
Lemma lem3606266 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606275 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (MK_COMB (@lem3606266 A) (@lem3606265 A)). Qed.
Lemma lem3606284 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term31 A s t x).
Proof. exact (eq_refl (term31 A s t x)). Qed.
Lemma lem3606285 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (fun_ext (fun x : A => @lem3606284 A s t x)). Qed.
Lemma lem3606286 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3606287 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3606286 A) (@lem3606285 A s t)). Qed.
Lemma lem3606288 {A : Type'} (t : A -> Prop) : (term44 A t) = (term44 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606287 A s t)). Qed.
Lemma lem3606289 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606290 {A : Type'} (t : A -> Prop) : (term46 A t) = (term46 A t).
Proof. exact (MK_COMB (@lem3606289 A) (@lem3606288 A t)). Qed.
Lemma lem3606291 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606290 A t)). Qed.
Lemma lem3606292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606293 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem3606292 A) (@lem3606291 A)). Qed.
Lemma lem3606318 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (TRANS (@lem3606275 A) (@lem3606293 A)). Qed.
Lemma lem3606319 {A : Type'} : (term50 A) = (term49 A).
Proof. exact (SYM (@lem3606318 A)). Qed.
Lemma lem3606322 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3606323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term29 A s t x) = (term51 A s t x).
Proof. exact (@lem3606322 (term29 A s t x)). Qed.
Lemma lem3606324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term29 A s t x).
Proof. exact (SYM (@lem3606323 A s t x)). Qed.
Lemma lem3606325 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term52 A s t x.
Proof. exact (h1). Qed.
Lemma lem3606331 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3606342 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term53 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3606347 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3606361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term53 A s t x.
Proof. exact (EQ_MP (@lem3606342 A s t x) (@lem3606325 A s t x h1)). Qed.
Lemma lem3606367 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3606377 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3606379 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term54 A s x.
Proof. exact (proj1 (@lem3606361 A s t x h1)). Qed.
Lemma lem3606383 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3606384 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term55 A s x.
Proof. exact (fun h0 : term54 A s x => @lem3606383 A s x h1). Qed.
Lemma lem3606386 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606387 {A : Type'} (s : A -> Prop) (x : A) : (term55 A s x) = (s x).
Proof. exact (@lem3606386 (s x)). Qed.
Lemma lem3606388 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3606387 A s x) (@lem3606384 A s x h1)). Qed.
Lemma lem3606391 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3606393 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term57 A s x).
Proof. exact (@lem3606391 (s x)). Qed.
Lemma lem3606396 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term57 A s x.
Proof. exact (EQ_MP (@lem3606393 A s x) (@lem3606379 A s t x h1)). Qed.
Lemma lem3606399 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (@lem3606396 A s t x h1 (@lem3606388 A s x h2)). Qed.
Lemma lem3606400 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : term58.
Proof. exact (fun h0 : ~ False => @lem3606399 A t s x h1 h2). Qed.
Lemma lem3606402 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606403 : term58 = False.
Proof. exact (@lem3606402 False). Qed.
Lemma lem3606404 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606403) (@lem3606400 A t s x h1 h2)). Qed.
Lemma lem3606405 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3606404 A t s x h1 h2) (fun h3 : False => @lem3606377 A s x h2)). Qed.
Lemma lem3606406 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606405 A t s x h1 h2) (@lem3606377 A s x h2)). Qed.
Lemma lem3606407 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3606406 A t s x h1 h2) (fun h3 : False => @lem3606367 A s x h2)). Qed.
Lemma lem3606408 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606407 A t s x h1 h2) (@lem3606367 A s x h2)). Qed.
Lemma lem3606409 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3606408 A t s x h1 h2) (fun h3 : False => @lem3606367 A s x h2)). Qed.
Lemma lem3606410 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606409 A t s x h1 h2) (@lem3606367 A s x h2)). Qed.
Lemma lem3606411 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3606410 A t s x h1 h2) (fun h3 : False => @lem3606347 A s x h2)). Qed.
Lemma lem3606412 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606411 A t s x h1 h2) (@lem3606347 A s x h2)). Qed.
Lemma lem3606413 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3606412 A t s x h1 h2) (fun h3 : False => @lem3606331 A s x h2)). Qed.
Lemma lem3606414 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606413 A t s x h1 h2) (@lem3606331 A s x h2)). Qed.
Lemma lem3606415 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : (term52 A s t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s t x => @lem3606414 A t s x h1 h2) (fun h3 : False => @lem3606325 A s t x h1)). Qed.
Lemma lem3606416 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3606415 A t s x h1 h2) (@lem3606325 A s t x h1)). Qed.
Lemma lem3606417 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) : term51 A s t x.
Proof. exact (fun h0 : term52 A s t x => @lem3606416 A t s x h0 h1). Qed.
Lemma lem3606418 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : s x) : term29 A s t x.
Proof. exact (EQ_MP (@lem3606324 A s t x) (@lem3606417 A t s x h1)). Qed.
Lemma lem3606419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term31 A s t x.
Proof. exact (fun h0 : s x => @lem3606418 A t s x h0). Qed.
Lemma lem3606424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term34 A s t.
Proof. exact (fun x : A => @lem3606419 A s t x). Qed.
Lemma lem3606429 {A : Type'} (t : A -> Prop) : term46 A t.
Proof. exact (fun s : A -> Prop => @lem3606424 A s t). Qed.
Lemma lem3606434 {A : Type'} : term50 A.
Proof. exact (fun t : A -> Prop => @lem3606429 A t). Qed.
Lemma lem3606435 {A : Type'} : term49 A.
Proof. exact (EQ_MP (@lem3606319 A) (@lem3606434 A)). Qed.
Lemma lem3606436 {A : Type'} (t : A -> Prop) : term59 A t.
Proof. exact (@lem3606435 A t). Qed.
Lemma lem3606437 {A : Type'} (t : A -> Prop) : (term59 A t) = (term45 A t).
Proof. exact (eq_refl (term59 A t)). Qed.
Lemma lem3606438 {A : Type'} (t : A -> Prop) : term45 A t.
Proof. exact (EQ_MP (@lem3606437 A t) (@lem3606436 A t)). Qed.
Lemma lem3606439 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term60 A t s.
Proof. exact (@lem3606438 A t s). Qed.
Lemma lem3606440 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term60 A t s) = (term36 A s t).
Proof. exact (eq_refl (term60 A t s)). Qed.
Lemma lem3606441 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (EQ_MP (@lem3606440 A s t) (@lem3606439 A t s)). Qed.
Lemma lem3606443 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (@lem3606234 A s t (@lem3606441 A s t)). Qed.
Lemma lem3606444 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A s t) : False.
Proof. exact (@lem3606443 A s t (@lem3606218 A s t h1)). Qed.
Lemma lem3606445 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A s t) : (term37 A s t) = False.
Proof. exact (prop_ext (fun h2 : term37 A s t => @lem3606444 A s t h1) (fun h2 : False => @lem3606218 A s t h1)). Qed.
Lemma lem3606446 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term37 A s t) : False.
Proof. exact (EQ_MP (@lem3606445 A s t h1) (@lem3606218 A s t h1)). Qed.
Lemma lem3606447 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (fun h0 : term37 A s t => @lem3606446 A s t h0). Qed.
Lemma lem3606448 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term34 A s t.
Proof. exact (EQ_MP (@lem3606217 A s t) (@lem3606447 A s t)). Qed.
Lemma lem3606449 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term22 A s t.
Proof. exact (EQ_MP (@lem3606213 A s t) (@lem3606448 A s t)). Qed.
Lemma lem3606450 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (EQ_MP (@lem3606171 A s t) (@lem3606449 A s t)). Qed.
Lemma lem3606452 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3606453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (@lem3606452 A s t). Qed.
Lemma lem3606454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term61 A s t).
Proof. exact (@lem3606453 A t (@UNION A s t)). Qed.
Lemma lem3606461 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term18 A s t).
Proof. exact (SYM (@lem3606454 A s t)). Qed.
Lemma lem3606469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606470 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606469 A P x). Qed.
Lemma lem3606471 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3606470 A t x). Qed.
Lemma lem3606472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3606473 {A : Type'} (t : A -> Prop) (x : A) : (term23 A x t) = (term24 A t x).
Proof. exact (MK_COMB (@lem3606472) (@lem3606471 A t x)). Qed.
Lemma lem3606475 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3606476 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3606475 A s x t). Qed.
Lemma lem3606480 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606481 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606480 A P x). Qed.
Lemma lem3606482 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3606481 A s x). Qed.
Lemma lem3606483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3606484 {A : Type'} (s : A -> Prop) (x : A) : (term27 A x s) = (term28 A s x).
Proof. exact (MK_COMB (@lem3606483) (@lem3606482 A s x)). Qed.
Lemma lem3606486 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3606487 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3606486 A P x). Qed.
Lemma lem3606488 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3606487 A t x). Qed.
Lemma lem3606489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term26 A s x t) = (term29 A s t x).
Proof. exact (MK_COMB (@lem3606484 A s x) (@lem3606488 A t x)). Qed.
Lemma lem3606492 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term25 A x s t) = (term29 A s t x).
Proof. exact (TRANS (@lem3606476 A s x t) (@lem3606489 A s t x)). Qed.
Lemma lem3606493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term62 A x s t) = (term63 A s t x).
Proof. exact (MK_COMB (@lem3606473 A t x) (@lem3606492 A s t x)). Qed.
Lemma lem3606496 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term65 A s t).
Proof. exact (fun_ext (fun x : A => @lem3606493 A s t x)). Qed.
Lemma lem3606497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3606498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term66 A s t).
Proof. exact (MK_COMB (@lem3606497 A) (@lem3606496 A s t)). Qed.
Lemma lem3606503 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term61 A s t).
Proof. exact (SYM (@lem3606498 A s t)). Qed.
Lemma lem3606505 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3606506 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term67 A s t).
Proof. exact (@lem3606505 (term66 A s t)). Qed.
Lemma lem3606507 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term66 A s t).
Proof. exact (SYM (@lem3606506 A s t)). Qed.
Lemma lem3606508 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term68 A s t) : term68 A s t.
Proof. exact (h1). Qed.
Lemma lem3606511 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term67 A s t) : term67 A s t.
Proof. exact (h1). Qed.
Lemma lem3606512 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term69 A s t.
Proof. exact (fun h0 : term67 A s t => @lem3606511 A s t h0). Qed.
Lemma lem3606513 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term69 A s t) : term69 A s t.
Proof. exact (h1). Qed.
Lemma lem3606514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term67 A s t) : term67 A s t.
Proof. exact (h1). Qed.
Lemma lem3606515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term67 A s t) (h2 : term69 A s t) : term67 A s t.
Proof. exact (@lem3606513 A s t h2 (@lem3606514 A s t h1)). Qed.
Lemma lem3606516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term67 A s t) : term70 A s t.
Proof. exact (fun h0 : term69 A s t => @lem3606515 A s t h1 h0). Qed.
Lemma lem3606517 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term69 A s t) : term69 A s t.
Proof. exact (h1). Qed.
Lemma lem3606518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term67 A s t) (h2 : term69 A s t) : term67 A s t.
Proof. exact (@lem3606516 A s t h1 (@lem3606517 A s t h2)). Qed.
Lemma lem3606519 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term69 A s t) : term69 A s t.
Proof. exact (fun h0 : term67 A s t => @lem3606518 A s t h0 h1). Qed.
Lemma lem3606520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term71 A s t.
Proof. exact (fun h0 : term69 A s t => @lem3606519 A s t h0). Qed.
Lemma lem3606523 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term69 A s t.
Proof. exact (@lem3606520 A s t (@lem3606512 A s t)). Qed.
Lemma lem3606524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term69 A s t.
Proof. exact (@lem3606523 A s t). Qed.
Lemma lem3606534 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3606535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term72 A s t).
Proof. exact (@lem3606534 (term68 A s t)). Qed.
Lemma lem3606537 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3606538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term72 A s t) = (term66 A s t).
Proof. exact (@lem3606537 (term66 A s t)). Qed.
Lemma lem3606543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term67 A s t) = (term66 A s t).
Proof. exact (TRANS (@lem3606535 A s t) (@lem3606538 A s t)). Qed.
Lemma lem3606548 {A : Type'} (t : A -> Prop) : (term73 A t) = (term74 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606543 A s t)). Qed.
Lemma lem3606549 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606550 {A : Type'} (t : A -> Prop) : (term75 A t) = (term76 A t).
Proof. exact (MK_COMB (@lem3606549 A) (@lem3606548 A t)). Qed.
Lemma lem3606555 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606550 A t)). Qed.
Lemma lem3606556 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606565 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (MK_COMB (@lem3606556 A) (@lem3606555 A)). Qed.
Lemma lem3606574 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term63 A s t x).
Proof. exact (eq_refl (term63 A s t x)). Qed.
Lemma lem3606575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term65 A s t) = (term65 A s t).
Proof. exact (fun_ext (fun x : A => @lem3606574 A s t x)). Qed.
Lemma lem3606576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3606577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term66 A s t) = (term66 A s t).
Proof. exact (MK_COMB (@lem3606576 A) (@lem3606575 A s t)). Qed.
Lemma lem3606578 {A : Type'} (t : A -> Prop) : (term74 A t) = (term74 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606577 A s t)). Qed.
Lemma lem3606579 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606580 {A : Type'} (t : A -> Prop) : (term76 A t) = (term76 A t).
Proof. exact (MK_COMB (@lem3606579 A) (@lem3606578 A t)). Qed.
Lemma lem3606581 {A : Type'} : (term78 A) = (term78 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606580 A t)). Qed.
Lemma lem3606582 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606583 {A : Type'} : (term80 A) = (term80 A).
Proof. exact (MK_COMB (@lem3606582 A) (@lem3606581 A)). Qed.
Lemma lem3606608 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (TRANS (@lem3606565 A) (@lem3606583 A)). Qed.
Lemma lem3606609 {A : Type'} : (term80 A) = (term79 A).
Proof. exact (SYM (@lem3606608 A)). Qed.
Lemma lem3606612 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3606613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term29 A s t x) = (term51 A s t x).
Proof. exact (@lem3606612 (term29 A s t x)). Qed.
Lemma lem3606614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term51 A s t x) = (term29 A s t x).
Proof. exact (SYM (@lem3606613 A s t x)). Qed.
Lemma lem3606615 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term52 A s t x.
Proof. exact (h1). Qed.
Lemma lem3606621 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3606632 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term53 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3606637 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3606651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term53 A s t x.
Proof. exact (EQ_MP (@lem3606632 A s t x) (@lem3606615 A s t x h1)). Qed.
Lemma lem3606657 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3606667 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3606671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term54 A t x.
Proof. exact (proj2 (@lem3606651 A s t x h1)). Qed.
Lemma lem3606673 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3606674 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term55 A t x.
Proof. exact (fun h0 : term54 A t x => @lem3606673 A t x h1). Qed.
Lemma lem3606676 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606677 {A : Type'} (t : A -> Prop) (x : A) : (term55 A t x) = (t x).
Proof. exact (@lem3606676 (t x)). Qed.
Lemma lem3606678 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3606677 A t x) (@lem3606674 A t x h1)). Qed.
Lemma lem3606681 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3606683 {A : Type'} (t : A -> Prop) (x : A) : (term54 A t x) = (term57 A t x).
Proof. exact (@lem3606681 (t x)). Qed.
Lemma lem3606686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) : term57 A t x.
Proof. exact (EQ_MP (@lem3606683 A t x) (@lem3606671 A s t x h1)). Qed.
Lemma lem3606689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (@lem3606686 A s t x h1 (@lem3606678 A t x h2)). Qed.
Lemma lem3606690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : term58.
Proof. exact (fun h0 : ~ False => @lem3606689 A s t x h1 h2). Qed.
Lemma lem3606692 (p : Prop) : (term56 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3606693 : term58 = False.
Proof. exact (@lem3606692 False). Qed.
Lemma lem3606694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606693) (@lem3606690 A s t x h1 h2)). Qed.
Lemma lem3606695 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3606694 A s t x h1 h2) (fun h3 : False => @lem3606667 A t x h2)). Qed.
Lemma lem3606696 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606695 A s t x h1 h2) (@lem3606667 A t x h2)). Qed.
Lemma lem3606697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3606696 A s t x h1 h2) (fun h3 : False => @lem3606657 A t x h2)). Qed.
Lemma lem3606698 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606697 A s t x h1 h2) (@lem3606657 A t x h2)). Qed.
Lemma lem3606699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3606698 A s t x h1 h2) (fun h3 : False => @lem3606657 A t x h2)). Qed.
Lemma lem3606700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606699 A s t x h1 h2) (@lem3606657 A t x h2)). Qed.
Lemma lem3606701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3606700 A s t x h1 h2) (fun h3 : False => @lem3606637 A t x h2)). Qed.
Lemma lem3606702 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606701 A s t x h1 h2) (@lem3606637 A t x h2)). Qed.
Lemma lem3606703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3606702 A s t x h1 h2) (fun h3 : False => @lem3606621 A t x h2)). Qed.
Lemma lem3606704 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606703 A s t x h1 h2) (@lem3606621 A t x h2)). Qed.
Lemma lem3606705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : (term52 A s t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s t x => @lem3606704 A s t x h1 h2) (fun h3 : False => @lem3606615 A s t x h1)). Qed.
Lemma lem3606706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term52 A s t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3606705 A s t x h1 h2) (@lem3606615 A s t x h1)). Qed.
Lemma lem3606707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) : term51 A s t x.
Proof. exact (fun h0 : term52 A s t x => @lem3606706 A s t x h0 h1). Qed.
Lemma lem3606708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) : term29 A s t x.
Proof. exact (EQ_MP (@lem3606614 A s t x) (@lem3606707 A s t x h1)). Qed.
Lemma lem3606709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term63 A s t x.
Proof. exact (fun h0 : t x => @lem3606708 A s t x h0). Qed.
Lemma lem3606714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term66 A s t.
Proof. exact (fun x : A => @lem3606709 A s t x). Qed.
Lemma lem3606719 {A : Type'} (t : A -> Prop) : term76 A t.
Proof. exact (fun s : A -> Prop => @lem3606714 A s t). Qed.
Lemma lem3606724 {A : Type'} : term80 A.
Proof. exact (fun t : A -> Prop => @lem3606719 A t). Qed.
Lemma lem3606725 {A : Type'} : term79 A.
Proof. exact (EQ_MP (@lem3606609 A) (@lem3606724 A)). Qed.
Lemma lem3606726 {A : Type'} (t : A -> Prop) : term81 A t.
Proof. exact (@lem3606725 A t). Qed.
Lemma lem3606727 {A : Type'} (t : A -> Prop) : (term81 A t) = (term75 A t).
Proof. exact (eq_refl (term81 A t)). Qed.
Lemma lem3606728 {A : Type'} (t : A -> Prop) : term75 A t.
Proof. exact (EQ_MP (@lem3606727 A t) (@lem3606726 A t)). Qed.
Lemma lem3606729 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term82 A t s.
Proof. exact (@lem3606728 A t s). Qed.
Lemma lem3606730 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A t s) = (term67 A s t).
Proof. exact (eq_refl (term82 A t s)). Qed.
Lemma lem3606731 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term67 A s t.
Proof. exact (EQ_MP (@lem3606730 A s t) (@lem3606729 A t s)). Qed.
Lemma lem3606733 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term67 A s t.
Proof. exact (@lem3606524 A s t (@lem3606731 A s t)). Qed.
Lemma lem3606734 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term68 A s t) : False.
Proof. exact (@lem3606733 A s t (@lem3606508 A s t h1)). Qed.
Lemma lem3606735 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term68 A s t) : (term68 A s t) = False.
Proof. exact (prop_ext (fun h2 : term68 A s t => @lem3606734 A s t h1) (fun h2 : False => @lem3606508 A s t h1)). Qed.
Lemma lem3606736 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term68 A s t) : False.
Proof. exact (EQ_MP (@lem3606735 A s t h1) (@lem3606508 A s t h1)). Qed.
Lemma lem3606737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term67 A s t.
Proof. exact (fun h0 : term68 A s t => @lem3606736 A s t h0). Qed.
Lemma lem3606738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term66 A s t.
Proof. exact (EQ_MP (@lem3606507 A s t) (@lem3606737 A s t)). Qed.
Lemma lem3606739 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term61 A s t.
Proof. exact (EQ_MP (@lem3606503 A s t) (@lem3606738 A s t)). Qed.
Lemma lem3606740 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (EQ_MP (@lem3606461 A s t) (@lem3606739 A s t)). Qed.
Lemma lem3606741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term19 A s t.
Proof. exact (EQ_MP (@lem3606160 A s t h1) (@lem3606740 A s t)). Qed.
Lemma lem3606742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term16 A s t.
Proof. exact (EQ_MP (@lem3606145 A s t h1) (@lem3606450 A s t)). Qed.
Lemma lem3606743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term7 A t.
Proof. exact (ex_intro (term8 A t) (@UNION A s t) (@lem3606741 A s t h1)). Qed.
Lemma lem3606744 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term7 A s.
Proof. exact (ex_intro (term8 A s) (@UNION A s t) (@lem3606742 A s t h1)). Qed.
Lemma lem3606745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : @FINITE A t.
Proof. exact (@lem3606130 A t (@lem3606743 A s t h1)). Qed.
Lemma lem3606746 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : @FINITE A s.
Proof. exact (@lem3606126 A s (@lem3606744 A s t h1)). Qed.
Lemma lem3606747 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term83 A s t.
Proof. exact (conj (@lem3606746 A s t h1) (@lem3606745 A s t h1)). Qed.
Lemma lem3606748 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : (term13 A s t) = (term83 A s t).
Proof. exact (prop_ext (fun h2 : term13 A s t => @lem3606747 A s t h1) (fun h2 : term83 A s t => @lem3606123 A s t h1)). Qed.
Lemma lem3606749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term13 A s t) : term83 A s t.
Proof. exact (EQ_MP (@lem3606748 A s t h1) (@lem3606123 A s t h1)). Qed.
Lemma lem3606750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term84 A s t.
Proof. exact (fun h0 : term13 A s t => @lem3606749 A s t h0). Qed.
Lemma lem3606751 {A : Type'} (s : A -> Prop) : term85 A s.
Proof. exact (@lem3606091 A s). Qed.
Lemma lem3606752 {A : Type'} (s : A -> Prop) : (term85 A s) = (term86 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem3606753 {A : Type'} (s : A -> Prop) : term86 A s.
Proof. exact (EQ_MP (@lem3606752 A s) (@lem3606751 A s)). Qed.
Lemma lem3606754 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term87 A s t.
Proof. exact (@lem3606753 A s t). Qed.
Lemma lem3606755 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term88 A s t).
Proof. exact (eq_refl (term87 A s t)). Qed.
Lemma lem3606758 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term88 A s t.
Proof. exact (EQ_MP (@lem3606755 A s t) (@lem3606754 A s t)). Qed.
Lemma lem3606759 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term88 A s t.
Proof. exact (@lem3606758 A s t). Qed.
Lemma lem3606760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term89 A s t.
Proof. exact (conj (@lem3606750 A s t) (@lem3606759 A s t)). Qed.
Lemma lem3606761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = ((term13 A s t) = (term83 A s t)).
Proof. exact (@lem32 (term13 A s t) (term83 A s t)). Qed.
Lemma lem3606762 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = (term83 A s t).
Proof. exact (EQ_MP (@lem3606761 A s t) (@lem3606760 A s t)). Qed.
Lemma lem3606767 {A : Type'} (s : A -> Prop) : term90 A s.
Proof. exact (fun t : A -> Prop => @lem3606762 A s t). Qed.
Lemma lem3606772 {A : Type'} : term91 A.
Proof. exact (fun s : A -> Prop => @lem3606767 A s). Qed.
