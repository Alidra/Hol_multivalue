Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_PSUBSET_TRANS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3226093 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3226094 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3226093 A s t). Qed.
Lemma lem3226101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3226101) (@lem3226094 A s t)). Qed.
Lemma lem3226104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3226105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (@lem3226104 A s t). Qed.
Lemma lem3226106 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term3 A t u).
Proof. exact (@lem3226105 A t u). Qed.
Lemma lem3226110 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3226111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3226110 A s t). Qed.
Lemma lem3226112 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term0 A t u).
Proof. exact (@lem3226111 A t u). Qed.
Lemma lem3226119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226120 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term1 A t u) = (term2 A t u).
Proof. exact (MK_COMB (@lem3226119) (@lem3226112 A t u)). Qed.
Lemma lem3226124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3226125 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3226124 A s t). Qed.
Lemma lem3226126 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (t = u) = (term4 A t u).
Proof. exact (@lem3226125 A t u). Qed.
Lemma lem3226135 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226136 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term5 A t u) = (term6 A t u).
Proof. exact (MK_COMB (@lem3226135) (@lem3226126 A t u)). Qed.
Lemma lem3226137 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term3 A t u) = (term7 A t u).
Proof. exact (MK_COMB (@lem3226120 A t u) (@lem3226136 A t u)). Qed.
Lemma lem3226140 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@PSUBSET A t u) = (term7 A t u).
Proof. exact (TRANS (@lem3226106 A t u) (@lem3226137 A t u)). Qed.
Lemma lem3226141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term8 A s t u) = (term9 A s t u).
Proof. exact (MK_COMB (@lem3226102 A s t) (@lem3226140 A t u)). Qed.
Lemma lem3226144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226145 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term10 A s t u) = (term11 A s t u).
Proof. exact (MK_COMB (@lem3226144) (@lem3226141 A s t u)). Qed.
Lemma lem3226147 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3226148 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (@lem3226147 A s t). Qed.
Lemma lem3226149 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term3 A s u).
Proof. exact (@lem3226148 A s u). Qed.
Lemma lem3226153 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3226154 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3226153 A s t). Qed.
Lemma lem3226155 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term0 A s u).
Proof. exact (@lem3226154 A s u). Qed.
Lemma lem3226162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226163 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term1 A s u) = (term2 A s u).
Proof. exact (MK_COMB (@lem3226162) (@lem3226155 A s u)). Qed.
Lemma lem3226167 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3226168 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3226167 A s t). Qed.
Lemma lem3226169 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (s = u) = (term4 A s u).
Proof. exact (@lem3226168 A s u). Qed.
Lemma lem3226178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226179 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term5 A s u) = (term6 A s u).
Proof. exact (MK_COMB (@lem3226178) (@lem3226169 A s u)). Qed.
Lemma lem3226180 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term3 A s u) = (term7 A s u).
Proof. exact (MK_COMB (@lem3226163 A s u) (@lem3226179 A s u)). Qed.
Lemma lem3226183 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@PSUBSET A s u) = (term7 A s u).
Proof. exact (TRANS (@lem3226149 A s u) (@lem3226180 A s u)). Qed.
Lemma lem3226184 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term12 A t s u) = (term13 A t s u).
Proof. exact (MK_COMB (@lem3226145 A s t u) (@lem3226183 A s u)). Qed.
Lemma lem3226187 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term14 A t s) = (term15 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3226184 A t s u)). Qed.
Lemma lem3226188 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226189 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term16 A t s) = (term17 A t s).
Proof. exact (MK_COMB (@lem3226188 A) (@lem3226187 A t s)). Qed.
Lemma lem3226194 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3226189 A t s)). Qed.
Lemma lem3226195 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226196 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (MK_COMB (@lem3226195 A) (@lem3226194 A s)). Qed.
Lemma lem3226201 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3226196 A s)). Qed.
Lemma lem3226202 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226203 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem3226202 A) (@lem3226201 A)). Qed.
Lemma lem3226208 {A : Type'} : (term25 A) = (term24 A).
Proof. exact (SYM (@lem3226203 A)). Qed.
Lemma lem3226232 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226233 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226232 A P x). Qed.
Lemma lem3226234 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3226233 A s x). Qed.
Lemma lem3226235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226236 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3226235) (@lem3226234 A s x)). Qed.
Lemma lem3226238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226239 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226238 A P x). Qed.
Lemma lem3226240 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3226239 A t x). Qed.
Lemma lem3226241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term28 A s x t) = (term29 A s t x).
Proof. exact (MK_COMB (@lem3226236 A s x) (@lem3226240 A t x)). Qed.
Lemma lem3226244 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term31 A s t).
Proof. exact (fun_ext (fun x : A => @lem3226241 A s t x)). Qed.
Lemma lem3226245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term32 A s t).
Proof. exact (MK_COMB (@lem3226245 A) (@lem3226244 A s t)). Qed.
Lemma lem3226251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226252 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3226251) (@lem3226246 A s t)). Qed.
Lemma lem3226262 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226263 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226262 A P x). Qed.
Lemma lem3226264 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3226263 A t x). Qed.
Lemma lem3226265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226266 {A : Type'} (t : A -> Prop) (x : A) : (term26 A x t) = (term27 A t x).
Proof. exact (MK_COMB (@lem3226265) (@lem3226264 A t x)). Qed.
Lemma lem3226268 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226269 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226268 A P x). Qed.
Lemma lem3226270 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3226269 A u x). Qed.
Lemma lem3226271 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term28 A t x u) = (term29 A t u x).
Proof. exact (MK_COMB (@lem3226266 A t x) (@lem3226270 A u x)). Qed.
Lemma lem3226274 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term30 A t u) = (term31 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226271 A t u x)). Qed.
Lemma lem3226275 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226276 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term0 A t u) = (term32 A t u).
Proof. exact (MK_COMB (@lem3226275 A) (@lem3226274 A t u)). Qed.
Lemma lem3226281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226282 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term2 A t u) = (term33 A t u).
Proof. exact (MK_COMB (@lem3226281) (@lem3226276 A t u)). Qed.
Lemma lem3226290 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226291 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226290 A P x). Qed.
Lemma lem3226292 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3226291 A t x). Qed.
Lemma lem3226293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226294 {A : Type'} (t : A -> Prop) (x : A) : (term34 A x t) = (term35 A t x).
Proof. exact (MK_COMB (@lem3226293) (@lem3226292 A t x)). Qed.
Lemma lem3226296 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226297 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226296 A P x). Qed.
Lemma lem3226298 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3226297 A u x). Qed.
Lemma lem3226299 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x t) = (@IN A x u)) = ((t x) = (u x)).
Proof. exact (MK_COMB (@lem3226294 A t x) (@lem3226298 A u x)). Qed.
Lemma lem3226302 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term36 A t u) = (term37 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226299 A t u x)). Qed.
Lemma lem3226303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226304 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term4 A t u) = (term38 A t u).
Proof. exact (MK_COMB (@lem3226303 A) (@lem3226302 A t u)). Qed.
Lemma lem3226309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226310 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term6 A t u) = (term39 A t u).
Proof. exact (MK_COMB (@lem3226309) (@lem3226304 A t u)). Qed.
Lemma lem3226311 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term7 A t u) = (term40 A t u).
Proof. exact (MK_COMB (@lem3226282 A t u) (@lem3226310 A t u)). Qed.
Lemma lem3226314 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term9 A s t u) = (term41 A s t u).
Proof. exact (MK_COMB (@lem3226252 A s t) (@lem3226311 A t u)). Qed.
Lemma lem3226317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226318 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term11 A s t u) = (term42 A s t u).
Proof. exact (MK_COMB (@lem3226317) (@lem3226314 A s t u)). Qed.
Lemma lem3226328 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226329 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226328 A P x). Qed.
Lemma lem3226330 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3226329 A s x). Qed.
Lemma lem3226331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226332 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3226331) (@lem3226330 A s x)). Qed.
Lemma lem3226334 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226335 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226334 A P x). Qed.
Lemma lem3226336 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3226335 A u x). Qed.
Lemma lem3226337 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term28 A s x u) = (term29 A s u x).
Proof. exact (MK_COMB (@lem3226332 A s x) (@lem3226336 A u x)). Qed.
Lemma lem3226340 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term30 A s u) = (term31 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226337 A s u x)). Qed.
Lemma lem3226341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226342 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term0 A s u) = (term32 A s u).
Proof. exact (MK_COMB (@lem3226341 A) (@lem3226340 A s u)). Qed.
Lemma lem3226347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226348 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term2 A s u) = (term33 A s u).
Proof. exact (MK_COMB (@lem3226347) (@lem3226342 A s u)). Qed.
Lemma lem3226356 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226357 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226356 A P x). Qed.
Lemma lem3226358 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3226357 A s x). Qed.
Lemma lem3226359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226360 {A : Type'} (s : A -> Prop) (x : A) : (term34 A x s) = (term35 A s x).
Proof. exact (MK_COMB (@lem3226359) (@lem3226358 A s x)). Qed.
Lemma lem3226362 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3226363 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3226362 A P x). Qed.
Lemma lem3226364 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3226363 A u x). Qed.
Lemma lem3226365 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x u)) = ((s x) = (u x)).
Proof. exact (MK_COMB (@lem3226360 A s x) (@lem3226364 A u x)). Qed.
Lemma lem3226368 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term36 A s u) = (term37 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226365 A s u x)). Qed.
Lemma lem3226369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226370 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term4 A s u) = (term38 A s u).
Proof. exact (MK_COMB (@lem3226369 A) (@lem3226368 A s u)). Qed.
Lemma lem3226375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226376 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term6 A s u) = (term39 A s u).
Proof. exact (MK_COMB (@lem3226375) (@lem3226370 A s u)). Qed.
Lemma lem3226377 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term7 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3226348 A s u) (@lem3226376 A s u)). Qed.
Lemma lem3226380 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term13 A t s u) = (term43 A t s u).
Proof. exact (MK_COMB (@lem3226318 A s t u) (@lem3226377 A s u)). Qed.
Lemma lem3226383 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term15 A t s) = (term44 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3226380 A t s u)). Qed.
Lemma lem3226384 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226385 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A t s) = (term45 A t s).
Proof. exact (MK_COMB (@lem3226384 A) (@lem3226383 A t s)). Qed.
Lemma lem3226390 {A : Type'} (s : A -> Prop) : (term19 A s) = (term46 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3226385 A t s)). Qed.
Lemma lem3226391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226392 {A : Type'} (s : A -> Prop) : (term21 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem3226391 A) (@lem3226390 A s)). Qed.
Lemma lem3226397 {A : Type'} : (term23 A) = (term48 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3226392 A s)). Qed.
Lemma lem3226398 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226399 {A : Type'} : (term25 A) = (term49 A).
Proof. exact (MK_COMB (@lem3226398 A) (@lem3226397 A)). Qed.
Lemma lem3226404 {A : Type'} : (term49 A) = (term25 A).
Proof. exact (SYM (@lem3226399 A)). Qed.
Lemma lem3226406 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3226407 {A : Type'} : (term49 A) = (term51 A).
Proof. exact (@lem3226406 (term49 A)). Qed.
Lemma lem3226408 {A : Type'} : (term51 A) = (term49 A).
Proof. exact (SYM (@lem3226407 A)). Qed.
Lemma lem3226409 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3226412 {A : Type'} (h1 : term51 A) : term51 A.
Proof. exact (h1). Qed.
Lemma lem3226413 {A : Type'} : term53 A.
Proof. exact (fun h0 : term51 A => @lem3226412 A h0). Qed.
Lemma lem3226414 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3226415 {A : Type'} (h1 : term51 A) : term51 A.
Proof. exact (h1). Qed.
Lemma lem3226416 {A : Type'} (h1 : term51 A) (h2 : term53 A) : term51 A.
Proof. exact (@lem3226414 A h2 (@lem3226415 A h1)). Qed.
Lemma lem3226417 {A : Type'} (h1 : term51 A) : term54 A.
Proof. exact (fun h0 : term53 A => @lem3226416 A h1 h0). Qed.
Lemma lem3226418 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3226419 {A : Type'} (h1 : term51 A) (h2 : term53 A) : term51 A.
Proof. exact (@lem3226417 A h1 (@lem3226418 A h2)). Qed.
Lemma lem3226420 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (fun h0 : term51 A => @lem3226419 A h0 h1). Qed.
Lemma lem3226421 {A : Type'} : term55 A.
Proof. exact (fun h0 : term53 A => @lem3226420 A h0). Qed.
Lemma lem3226424 {A : Type'} : term53 A.
Proof. exact (@lem3226421 A (@lem3226413 A)). Qed.
Lemma lem3226425 {A : Type'} : term53 A.
Proof. exact (@lem3226424 A). Qed.
Lemma lem3226427 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3226428 {A : Type'} : (term51 A) = (term56 A).
Proof. exact (@lem3226427 (term52 A)). Qed.
Lemma lem3226430 (t : Prop) : (term57 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3226431 {A : Type'} : (term56 A) = (term49 A).
Proof. exact (@lem3226430 (term49 A)). Qed.
Lemma lem3226482 {A : Type'} : (term51 A) = (term49 A).
Proof. exact (TRANS (@lem3226428 A) (@lem3226431 A)). Qed.
Lemma lem3226487 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = ((s x) = (u x)).
Proof. exact (eq_refl ((s x) = (u x))). Qed.
Lemma lem3226488 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term37 A s u) = (term37 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226487 A s u x)). Qed.
Lemma lem3226489 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226490 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term38 A s u) = (term38 A s u).
Proof. exact (MK_COMB (@lem3226489 A) (@lem3226488 A s u)). Qed.
Lemma lem3226491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226492 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term39 A s u) = (term39 A s u).
Proof. exact (MK_COMB (@lem3226491) (@lem3226490 A s u)). Qed.
Lemma lem3226497 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term29 A s u x) = (term29 A s u x).
Proof. exact (eq_refl (term29 A s u x)). Qed.
Lemma lem3226498 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term31 A s u) = (term31 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226497 A s u x)). Qed.
Lemma lem3226499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226500 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term32 A s u) = (term32 A s u).
Proof. exact (MK_COMB (@lem3226499 A) (@lem3226498 A s u)). Qed.
Lemma lem3226501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226502 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term33 A s u) = (term33 A s u).
Proof. exact (MK_COMB (@lem3226501) (@lem3226500 A s u)). Qed.
Lemma lem3226503 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term40 A s u).
Proof. exact (MK_COMB (@lem3226502 A s u) (@lem3226492 A s u)). Qed.
Lemma lem3226508 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : ((t x) = (u x)) = ((t x) = (u x)).
Proof. exact (eq_refl ((t x) = (u x))). Qed.
Lemma lem3226509 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term37 A t u) = (term37 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226508 A t u x)). Qed.
Lemma lem3226510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226511 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term38 A t u) = (term38 A t u).
Proof. exact (MK_COMB (@lem3226510 A) (@lem3226509 A t u)). Qed.
Lemma lem3226512 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226513 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term39 A t u) = (term39 A t u).
Proof. exact (MK_COMB (@lem3226512) (@lem3226511 A t u)). Qed.
Lemma lem3226518 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term29 A t u x) = (term29 A t u x).
Proof. exact (eq_refl (term29 A t u x)). Qed.
Lemma lem3226519 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term31 A t u) = (term31 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226518 A t u x)). Qed.
Lemma lem3226520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226521 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term32 A t u) = (term32 A t u).
Proof. exact (MK_COMB (@lem3226520 A) (@lem3226519 A t u)). Qed.
Lemma lem3226522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226523 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term33 A t u).
Proof. exact (MK_COMB (@lem3226522) (@lem3226521 A t u)). Qed.
Lemma lem3226524 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term40 A t u) = (term40 A t u).
Proof. exact (MK_COMB (@lem3226523 A t u) (@lem3226513 A t u)). Qed.
Lemma lem3226529 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term29 A s t x) = (term29 A s t x).
Proof. exact (eq_refl (term29 A s t x)). Qed.
Lemma lem3226530 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term31 A s t).
Proof. exact (fun_ext (fun x : A => @lem3226529 A s t x)). Qed.
Lemma lem3226531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term32 A s t).
Proof. exact (MK_COMB (@lem3226531 A) (@lem3226530 A s t)). Qed.
Lemma lem3226533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226534 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3226533) (@lem3226532 A s t)). Qed.
Lemma lem3226535 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term41 A s t u) = (term41 A s t u).
Proof. exact (MK_COMB (@lem3226534 A s t) (@lem3226524 A t u)). Qed.
Lemma lem3226536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3226537 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term42 A s t u) = (term42 A s t u).
Proof. exact (MK_COMB (@lem3226536) (@lem3226535 A s t u)). Qed.
Lemma lem3226538 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term43 A t s u) = (term43 A t s u).
Proof. exact (MK_COMB (@lem3226537 A s t u) (@lem3226503 A s u)). Qed.
Lemma lem3226539 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term44 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3226538 A t s u)). Qed.
Lemma lem3226540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226541 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term45 A t s).
Proof. exact (MK_COMB (@lem3226540 A) (@lem3226539 A t s)). Qed.
Lemma lem3226542 {A : Type'} (s : A -> Prop) : (term46 A s) = (term46 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3226541 A t s)). Qed.
Lemma lem3226543 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226544 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem3226543 A) (@lem3226542 A s)). Qed.
Lemma lem3226545 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3226544 A s)). Qed.
Lemma lem3226546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3226547 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (MK_COMB (@lem3226546 A) (@lem3226545 A)). Qed.
Lemma lem3226612 {A : Type'} : (term51 A) = (term49 A).
Proof. exact (TRANS (@lem3226482 A) (@lem3226547 A)). Qed.
Lemma lem3226613 {A : Type'} : (term49 A) = (term51 A).
Proof. exact (SYM (@lem3226612 A)). Qed.
Lemma lem3226614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term41 A s t u) : term41 A s t u.
Proof. exact (h1). Qed.
Lemma lem3226616 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3226617 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term40 A s u) = (term58 A s u).
Proof. exact (@lem3226616 (term40 A s u)). Qed.
Lemma lem3226618 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term58 A s u) = (term40 A s u).
Proof. exact (SYM (@lem3226617 A s u)). Qed.
Lemma lem3226619 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term59 A s u) : term59 A s u.
Proof. exact (h1). Qed.
Lemma lem3226626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term29 A s t x) = (term60 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3226627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term61 A s t).
Proof. exact (fun_ext (fun x : A => @lem3226626 A s t x)). Qed.
Lemma lem3226628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3226628 A) (@lem3226627 A s t)). Qed.
Lemma lem3226636 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term29 A t u x) = (term60 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem3226637 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term31 A t u) = (term61 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226636 A t u x)). Qed.
Lemma lem3226638 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226639 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term32 A t u) = (term62 A t u).
Proof. exact (MK_COMB (@lem3226638 A) (@lem3226637 A t u)). Qed.
Lemma lem3226654 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term63 A t u x) = (term64 A t u x).
Proof. exact (@lem17646 (t x) (u x)). Qed.
Lemma lem3226655 {A : Type'} (P : A -> Prop) : (term65 A P) = (term66 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3226656 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term39 A t u) = (term67 A t u).
Proof. exact (@lem3226655 A (term37 A t u)). Qed.
Lemma lem3226657 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term68 A t u x) = ((t x) = (u x)).
Proof. exact (eq_refl (term68 A t u x)). Qed.
Lemma lem3226658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226659 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term69 A t u x) = (term63 A t u x).
Proof. exact (MK_COMB (@lem3226658) (@lem3226657 A t u x)). Qed.
Lemma lem3226660 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term69 A t u x) = (term64 A t u x).
Proof. exact (TRANS (@lem3226659 A t u x) (@lem3226654 A t u x)). Qed.
Lemma lem3226661 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term70 A t u) = (term71 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226660 A t u x)). Qed.
Lemma lem3226662 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226663 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term67 A t u) = (term72 A t u).
Proof. exact (MK_COMB (@lem3226662 A) (@lem3226661 A t u)). Qed.
Lemma lem3226664 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term39 A t u) = (term72 A t u).
Proof. exact (TRANS (@lem3226656 A t u) (@lem3226663 A t u)). Qed.
Lemma lem3226665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226666 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term33 A t u) = (term73 A t u).
Proof. exact (MK_COMB (@lem3226665) (@lem3226639 A t u)). Qed.
Lemma lem3226667 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term40 A t u) = (term74 A t u).
Proof. exact (MK_COMB (@lem3226666 A t u) (@lem3226664 A t u)). Qed.
Lemma lem3226668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226669 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term73 A s t).
Proof. exact (MK_COMB (@lem3226668) (@lem3226629 A s t)). Qed.
Lemma lem3226670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term41 A s t u) = (term75 A s t u).
Proof. exact (MK_COMB (@lem3226669 A s t) (@lem3226667 A t u)). Qed.
Lemma lem3226736 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3226737 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (@lem3226736 A P Q). Qed.
Lemma lem3226738 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term78 A t u) = (term79 A t u).
Proof. exact (@lem3226737 A (term80 A t u) (term81 A t u)). Qed.
Lemma lem3226739 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A t u x) = (term83 A t u x).
Proof. exact (eq_refl (term82 A t u x)). Qed.
Lemma lem3226740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3226741 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term84 A t u x) = (term85 A t u x).
Proof. exact (MK_COMB (@lem3226740) (@lem3226739 A t u x)). Qed.
Lemma lem3226742 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3226743 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term64 A t u x).
Proof. exact (MK_COMB (@lem3226741 A t u x) (@lem3226742 A t u x)). Qed.
Lemma lem3226744 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term89 A t u) = (term71 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226743 A t u x)). Qed.
Lemma lem3226745 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226746 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term78 A t u) = (term72 A t u).
Proof. exact (MK_COMB (@lem3226745 A) (@lem3226744 A t u)). Qed.
Lemma lem3226747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226748 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term90 A t u) = (term91 A t u).
Proof. exact (MK_COMB (@lem3226747) (@lem3226746 A t u)). Qed.
Lemma lem3226749 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A t u x) = (term83 A t u x).
Proof. exact (eq_refl (term82 A t u x)). Qed.
Lemma lem3226750 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term92 A t u) = (term80 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226749 A t u x)). Qed.
Lemma lem3226751 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226752 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term93 A t u) = (term94 A t u).
Proof. exact (MK_COMB (@lem3226751 A) (@lem3226750 A t u)). Qed.
Lemma lem3226753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3226754 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term95 A t u) = (term96 A t u).
Proof. exact (MK_COMB (@lem3226753) (@lem3226752 A t u)). Qed.
Lemma lem3226755 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3226756 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term81 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226755 A t u x)). Qed.
Lemma lem3226757 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226758 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term98 A t u) = (term99 A t u).
Proof. exact (MK_COMB (@lem3226757 A) (@lem3226756 A t u)). Qed.
Lemma lem3226759 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term79 A t u) = (term100 A t u).
Proof. exact (MK_COMB (@lem3226754 A t u) (@lem3226758 A t u)). Qed.
Lemma lem3226760 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term78 A t u) = (term79 A t u)) = ((term72 A t u) = (term100 A t u)).
Proof. exact (MK_COMB (@lem3226748 A t u) (@lem3226759 A t u)). Qed.
Lemma lem3226761 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term72 A t u) = (term100 A t u).
Proof. exact (EQ_MP (@lem3226760 A t u) (@lem3226738 A t u)). Qed.
Lemma lem3226822 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term73 A t u).
Proof. exact (eq_refl (term73 A t u)). Qed.
Lemma lem3226823 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term74 A t u) = (term101 A t u).
Proof. exact (MK_COMB (@lem3226822 A t u) (@lem3226761 A t u)). Qed.
Lemma lem3226824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term73 A s t).
Proof. exact (eq_refl (term73 A s t)). Qed.
Lemma lem3226825 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term75 A s t u) = (term102 A s t u).
Proof. exact (MK_COMB (@lem3226824 A s t) (@lem3226823 A t u)). Qed.
Lemma lem3226827 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3226828 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (@lem3226827 A P Q). Qed.
Lemma lem3226829 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term79 A t u) = (term78 A t u).
Proof. exact (@lem3226828 A (term80 A t u) (term81 A t u)). Qed.
Lemma lem3226830 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A t u x) = (term83 A t u x).
Proof. exact (eq_refl (term82 A t u x)). Qed.
Lemma lem3226831 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term92 A t u) = (term80 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226830 A t u x)). Qed.
Lemma lem3226832 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226833 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term93 A t u) = (term94 A t u).
Proof. exact (MK_COMB (@lem3226832 A) (@lem3226831 A t u)). Qed.
Lemma lem3226834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3226835 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term95 A t u) = (term96 A t u).
Proof. exact (MK_COMB (@lem3226834) (@lem3226833 A t u)). Qed.
Lemma lem3226836 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3226837 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term97 A t u) = (term81 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226836 A t u x)). Qed.
Lemma lem3226838 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226839 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term98 A t u) = (term99 A t u).
Proof. exact (MK_COMB (@lem3226838 A) (@lem3226837 A t u)). Qed.
Lemma lem3226840 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term79 A t u) = (term100 A t u).
Proof. exact (MK_COMB (@lem3226835 A t u) (@lem3226839 A t u)). Qed.
Lemma lem3226841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226842 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term103 A t u) = (term104 A t u).
Proof. exact (MK_COMB (@lem3226841) (@lem3226840 A t u)). Qed.
Lemma lem3226843 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term82 A t u x) = (term83 A t u x).
Proof. exact (eq_refl (term82 A t u x)). Qed.
Lemma lem3226844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3226845 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term84 A t u x) = (term85 A t u x).
Proof. exact (MK_COMB (@lem3226844) (@lem3226843 A t u x)). Qed.
Lemma lem3226846 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term86 A t u x) = (term87 A t u x).
Proof. exact (eq_refl (term86 A t u x)). Qed.
Lemma lem3226847 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term88 A t u x) = (term64 A t u x).
Proof. exact (MK_COMB (@lem3226845 A t u x) (@lem3226846 A t u x)). Qed.
Lemma lem3226848 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term89 A t u) = (term71 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226847 A t u x)). Qed.
Lemma lem3226849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226850 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term78 A t u) = (term72 A t u).
Proof. exact (MK_COMB (@lem3226849 A) (@lem3226848 A t u)). Qed.
Lemma lem3226851 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term79 A t u) = (term78 A t u)) = ((term100 A t u) = (term72 A t u)).
Proof. exact (MK_COMB (@lem3226842 A t u) (@lem3226850 A t u)). Qed.
Lemma lem3226852 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term100 A t u) = (term72 A t u).
Proof. exact (EQ_MP (@lem3226851 A t u) (@lem3226829 A t u)). Qed.
Lemma lem3226853 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term73 A t u).
Proof. exact (eq_refl (term73 A t u)). Qed.
Lemma lem3226854 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = (term74 A t u).
Proof. exact (MK_COMB (@lem3226853 A t u) (@lem3226852 A t u)). Qed.
Lemma lem3226856 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3226857 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (@lem3226856 A P Q). Qed.
Lemma lem3226858 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term107 A t u) = (term108 A t u).
Proof. exact (@lem3226857 A (term62 A t u) (term71 A t u)). Qed.
Lemma lem3226859 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term109 A t u x) = (term64 A t u x).
Proof. exact (eq_refl (term109 A t u x)). Qed.
Lemma lem3226860 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term110 A t u) = (term71 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226859 A t u x)). Qed.
Lemma lem3226861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226862 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term111 A t u) = (term72 A t u).
Proof. exact (MK_COMB (@lem3226861 A) (@lem3226860 A t u)). Qed.
Lemma lem3226863 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term73 A t u).
Proof. exact (eq_refl (term73 A t u)). Qed.
Lemma lem3226864 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term107 A t u) = (term74 A t u).
Proof. exact (MK_COMB (@lem3226863 A t u) (@lem3226862 A t u)). Qed.
Lemma lem3226865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226866 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term112 A t u) = (term113 A t u).
Proof. exact (MK_COMB (@lem3226865) (@lem3226864 A t u)). Qed.
Lemma lem3226867 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term109 A t u x) = (term64 A t u x).
Proof. exact (eq_refl (term109 A t u x)). Qed.
Lemma lem3226868 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term73 A t u).
Proof. exact (eq_refl (term73 A t u)). Qed.
Lemma lem3226869 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term114 A t u x) = (term115 A t u x).
Proof. exact (MK_COMB (@lem3226868 A t u) (@lem3226867 A t u x)). Qed.
Lemma lem3226870 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term116 A t u) = (term117 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226869 A t u x)). Qed.
Lemma lem3226871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226872 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term108 A t u) = (term118 A t u).
Proof. exact (MK_COMB (@lem3226871 A) (@lem3226870 A t u)). Qed.
Lemma lem3226873 {A : Type'} (t : A -> Prop) (u : A -> Prop) : ((term107 A t u) = (term108 A t u)) = ((term74 A t u) = (term118 A t u)).
Proof. exact (MK_COMB (@lem3226866 A t u) (@lem3226872 A t u)). Qed.
Lemma lem3226874 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term74 A t u) = (term118 A t u).
Proof. exact (EQ_MP (@lem3226873 A t u) (@lem3226858 A t u)). Qed.
Lemma lem3226875 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term101 A t u) = (term118 A t u).
Proof. exact (TRANS (@lem3226854 A t u) (@lem3226874 A t u)). Qed.
Lemma lem3226876 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term73 A s t).
Proof. exact (eq_refl (term73 A s t)). Qed.
Lemma lem3226877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term102 A s t u) = (term119 A s t u).
Proof. exact (MK_COMB (@lem3226876 A s t) (@lem3226875 A t u)). Qed.
Lemma lem3226879 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3226880 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (@lem3226879 A P Q). Qed.
Lemma lem3226881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term120 A s t u) = (term121 A s t u).
Proof. exact (@lem3226880 A (term62 A s t) (term117 A t u)). Qed.
Lemma lem3226882 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term122 A t u x) = (term115 A t u x).
Proof. exact (eq_refl (term122 A t u x)). Qed.
Lemma lem3226883 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term123 A t u) = (term117 A t u).
Proof. exact (fun_ext (fun x : A => @lem3226882 A t u x)). Qed.
Lemma lem3226884 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226885 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term124 A t u) = (term118 A t u).
Proof. exact (MK_COMB (@lem3226884 A) (@lem3226883 A t u)). Qed.
Lemma lem3226886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term73 A s t).
Proof. exact (eq_refl (term73 A s t)). Qed.
Lemma lem3226887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term120 A s t u) = (term119 A s t u).
Proof. exact (MK_COMB (@lem3226886 A s t) (@lem3226885 A t u)). Qed.
Lemma lem3226888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term125 A s t u) = (term126 A s t u).
Proof. exact (MK_COMB (@lem3226888) (@lem3226887 A s t u)). Qed.
Lemma lem3226890 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term122 A t u x) = (term115 A t u x).
Proof. exact (eq_refl (term122 A t u x)). Qed.
Lemma lem3226891 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term73 A s t).
Proof. exact (eq_refl (term73 A s t)). Qed.
Lemma lem3226892 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term127 A s t u x) = (term128 A s t u x).
Proof. exact (MK_COMB (@lem3226891 A s t) (@lem3226890 A t u x)). Qed.
Lemma lem3226893 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term129 A s t u) = (term130 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3226892 A s t u x)). Qed.
Lemma lem3226894 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term121 A s t u) = (term131 A s t u).
Proof. exact (MK_COMB (@lem3226894 A) (@lem3226893 A s t u)). Qed.
Lemma lem3226896 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term120 A s t u) = (term121 A s t u)) = ((term119 A s t u) = (term131 A s t u)).
Proof. exact (MK_COMB (@lem3226889 A s t u) (@lem3226895 A s t u)). Qed.
Lemma lem3226897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term119 A s t u) = (term131 A s t u).
Proof. exact (EQ_MP (@lem3226896 A s t u) (@lem3226881 A s t u)). Qed.
Lemma lem3226898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term102 A s t u) = (term131 A s t u).
Proof. exact (TRANS (@lem3226877 A s t u) (@lem3226897 A s t u)). Qed.
Lemma lem3226899 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term75 A s t u) = (term131 A s t u).
Proof. exact (TRANS (@lem3226825 A s t u) (@lem3226898 A s t u)). Qed.
Lemma lem3226900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term41 A s t u) = (term131 A s t u).
Proof. exact (TRANS (@lem3226670 A s t u) (@lem3226899 A s t u)). Qed.
Lemma lem3226901 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term41 A s t u) : term131 A s t u.
Proof. exact (EQ_MP (@lem3226900 A s t u) (@lem3226614 A s t u h1)). Qed.
Lemma lem3226908 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term132 A s u x) = (term83 A s u x).
Proof. exact (@lem17362 (s x) (u x)). Qed.
Lemma lem3226909 {A : Type'} (P : A -> Prop) : (term65 A P) = (term66 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3226910 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term133 A s u) = (term134 A s u).
Proof. exact (@lem3226909 A (term31 A s u)). Qed.
Lemma lem3226911 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term135 A s u x) = (term29 A s u x).
Proof. exact (eq_refl (term135 A s u x)). Qed.
Lemma lem3226912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3226913 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term136 A s u x) = (term132 A s u x).
Proof. exact (MK_COMB (@lem3226912) (@lem3226911 A s u x)). Qed.
Lemma lem3226914 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term136 A s u x) = (term83 A s u x).
Proof. exact (TRANS (@lem3226913 A s u x) (@lem3226908 A s u x)). Qed.
Lemma lem3226915 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term137 A s u) = (term80 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226914 A s u x)). Qed.
Lemma lem3226916 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3226917 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term134 A s u) = (term94 A s u).
Proof. exact (MK_COMB (@lem3226916 A) (@lem3226915 A s u)). Qed.
Lemma lem3226918 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term133 A s u) = (term94 A s u).
Proof. exact (TRANS (@lem3226910 A s u) (@lem3226917 A s u)). Qed.
Lemma lem3226933 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : ((s x) = (u x)) = (term138 A s u x).
Proof. exact (@lem17784 (s x) (u x)). Qed.
Lemma lem3226934 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term37 A s u) = (term139 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226933 A s u x)). Qed.
Lemma lem3226935 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226936 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term38 A s u) = (term140 A s u).
Proof. exact (MK_COMB (@lem3226935 A) (@lem3226934 A s u)). Qed.
Lemma lem3226937 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term141 A s u) = (term38 A s u).
Proof. exact (@lem16933 (term38 A s u)). Qed.
Lemma lem3226938 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term141 A s u) = (term140 A s u).
Proof. exact (TRANS (@lem3226937 A s u) (@lem3226936 A s u)). Qed.
Lemma lem3226939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3226940 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term142 A s u) = (term96 A s u).
Proof. exact (MK_COMB (@lem3226939) (@lem3226918 A s u)). Qed.
Lemma lem3226941 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term143 A s u) = (term144 A s u).
Proof. exact (MK_COMB (@lem3226940 A s u) (@lem3226938 A s u)). Qed.
Lemma lem3226942 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term59 A s u) = (term143 A s u).
Proof. exact (@lem17045 (term32 A s u) (term39 A s u)). Qed.
Lemma lem3226943 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term59 A s u) = (term144 A s u).
Proof. exact (TRANS (@lem3226942 A s u) (@lem3226941 A s u)). Qed.
Lemma lem3226973 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3226974 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (@lem3226973 A P Q). Qed.
Lemma lem3226975 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term147 A s u) = (term148 A s u).
Proof. exact (@lem3226974 A (term149 A s u) (term61 A s u)). Qed.
Lemma lem3226976 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term150 A s u x) = (term151 A s u x).
Proof. exact (eq_refl (term150 A s u x)). Qed.
Lemma lem3226977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226978 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term152 A s u x) = (term153 A s u x).
Proof. exact (MK_COMB (@lem3226977) (@lem3226976 A s u x)). Qed.
Lemma lem3226979 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term154 A s u x) = (term60 A s u x).
Proof. exact (eq_refl (term154 A s u x)). Qed.
Lemma lem3226980 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term155 A s u x) = (term138 A s u x).
Proof. exact (MK_COMB (@lem3226978 A s u x) (@lem3226979 A s u x)). Qed.
Lemma lem3226981 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term156 A s u) = (term139 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226980 A s u x)). Qed.
Lemma lem3226982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226983 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term147 A s u) = (term140 A s u).
Proof. exact (MK_COMB (@lem3226982 A) (@lem3226981 A s u)). Qed.
Lemma lem3226984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3226985 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term157 A s u) = (term158 A s u).
Proof. exact (MK_COMB (@lem3226984) (@lem3226983 A s u)). Qed.
Lemma lem3226986 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term150 A s u x) = (term151 A s u x).
Proof. exact (eq_refl (term150 A s u x)). Qed.
Lemma lem3226987 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term159 A s u) = (term149 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226986 A s u x)). Qed.
Lemma lem3226988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226989 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term160 A s u) = (term161 A s u).
Proof. exact (MK_COMB (@lem3226988 A) (@lem3226987 A s u)). Qed.
Lemma lem3226990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3226991 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term162 A s u) = (term163 A s u).
Proof. exact (MK_COMB (@lem3226990) (@lem3226989 A s u)). Qed.
Lemma lem3226992 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term154 A s u x) = (term60 A s u x).
Proof. exact (eq_refl (term154 A s u x)). Qed.
Lemma lem3226993 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term164 A s u) = (term61 A s u).
Proof. exact (fun_ext (fun x : A => @lem3226992 A s u x)). Qed.
Lemma lem3226994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3226995 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term165 A s u) = (term62 A s u).
Proof. exact (MK_COMB (@lem3226994 A) (@lem3226993 A s u)). Qed.
Lemma lem3226996 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term148 A s u) = (term166 A s u).
Proof. exact (MK_COMB (@lem3226991 A s u) (@lem3226995 A s u)). Qed.
Lemma lem3226997 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term147 A s u) = (term148 A s u)) = ((term140 A s u) = (term166 A s u)).
Proof. exact (MK_COMB (@lem3226985 A s u) (@lem3226996 A s u)). Qed.
Lemma lem3226998 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term140 A s u) = (term166 A s u).
Proof. exact (EQ_MP (@lem3226997 A s u) (@lem3226975 A s u)). Qed.
Lemma lem3227059 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term96 A s u) = (term96 A s u).
Proof. exact (eq_refl (term96 A s u)). Qed.
Lemma lem3227060 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term167 A s u).
Proof. exact (MK_COMB (@lem3227059 A s u) (@lem3226998 A s u)). Qed.
Lemma lem3227062 {A : Type'} (P : A -> Prop) (Q : Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3227063 {A : Type'} (P : A -> Prop) (Q : Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (@lem3227062 A P Q). Qed.
Lemma lem3227064 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term170 A s u) = (term171 A s u).
Proof. exact (@lem3227063 A (term80 A s u) (term166 A s u)). Qed.
Lemma lem3227065 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term82 A s u x) = (term83 A s u x).
Proof. exact (eq_refl (term82 A s u x)). Qed.
Lemma lem3227066 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term92 A s u) = (term80 A s u).
Proof. exact (fun_ext (fun x : A => @lem3227065 A s u x)). Qed.
Lemma lem3227067 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3227068 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term93 A s u) = (term94 A s u).
Proof. exact (MK_COMB (@lem3227067 A) (@lem3227066 A s u)). Qed.
Lemma lem3227069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3227070 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term95 A s u) = (term96 A s u).
Proof. exact (MK_COMB (@lem3227069) (@lem3227068 A s u)). Qed.
Lemma lem3227071 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term166 A s u).
Proof. exact (eq_refl (term166 A s u)). Qed.
Lemma lem3227072 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term170 A s u) = (term167 A s u).
Proof. exact (MK_COMB (@lem3227070 A s u) (@lem3227071 A s u)). Qed.
Lemma lem3227073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227074 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term172 A s u) = (term173 A s u).
Proof. exact (MK_COMB (@lem3227073) (@lem3227072 A s u)). Qed.
Lemma lem3227075 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term82 A s u x) = (term83 A s u x).
Proof. exact (eq_refl (term82 A s u x)). Qed.
Lemma lem3227076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3227077 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term84 A s u x) = (term85 A s u x).
Proof. exact (MK_COMB (@lem3227076) (@lem3227075 A s u x)). Qed.
Lemma lem3227078 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term166 A s u).
Proof. exact (eq_refl (term166 A s u)). Qed.
Lemma lem3227079 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term174 A x s u) = (term175 A x s u).
Proof. exact (MK_COMB (@lem3227077 A s u x) (@lem3227078 A s u)). Qed.
Lemma lem3227080 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term176 A s u) = (term177 A s u).
Proof. exact (fun_ext (fun x : A => @lem3227079 A x s u)). Qed.
Lemma lem3227081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3227082 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term171 A s u) = (term178 A s u).
Proof. exact (MK_COMB (@lem3227081 A) (@lem3227080 A s u)). Qed.
Lemma lem3227083 {A : Type'} (s : A -> Prop) (u : A -> Prop) : ((term170 A s u) = (term171 A s u)) = ((term167 A s u) = (term178 A s u)).
Proof. exact (MK_COMB (@lem3227074 A s u) (@lem3227082 A s u)). Qed.
Lemma lem3227084 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term167 A s u) = (term178 A s u).
Proof. exact (EQ_MP (@lem3227083 A s u) (@lem3227064 A s u)). Qed.
Lemma lem3227085 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term178 A s u).
Proof. exact (TRANS (@lem3227060 A s u) (@lem3227084 A s u)). Qed.
Lemma lem3227086 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term59 A s u) = (term178 A s u).
Proof. exact (TRANS (@lem3226943 A s u) (@lem3227085 A s u)). Qed.
Lemma lem3227087 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term59 A s u) : term178 A s u.
Proof. exact (EQ_MP (@lem3227086 A s u) (@lem3226619 A s u h1)). Qed.
Lemma lem3227088 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term175 A x s u) : term175 A x s u.
Proof. exact (h1). Qed.
Lemma lem3227089 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term128 A s t u x'.
Proof. exact (h1). Qed.
Lemma lem3227100 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term60 A s u x) = (term60 A s u x).
Proof. exact (eq_refl (term60 A s u x)). Qed.
Lemma lem3227101 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term61 A s u) = (term61 A s u).
Proof. exact (fun_ext (fun x : A => @lem3227100 A s u x)). Qed.
Lemma lem3227102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227103 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term62 A s u) = (term62 A s u).
Proof. exact (MK_COMB (@lem3227102 A) (@lem3227101 A s u)). Qed.
Lemma lem3227114 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term151 A s u x) = (term151 A s u x).
Proof. exact (eq_refl (term151 A s u x)). Qed.
Lemma lem3227115 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term149 A s u) = (term149 A s u).
Proof. exact (fun_ext (fun x : A => @lem3227114 A s u x)). Qed.
Lemma lem3227116 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227117 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term161 A s u) = (term161 A s u).
Proof. exact (MK_COMB (@lem3227116 A) (@lem3227115 A s u)). Qed.
Lemma lem3227118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3227119 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term163 A s u) = (term163 A s u).
Proof. exact (MK_COMB (@lem3227118) (@lem3227117 A s u)). Qed.
Lemma lem3227120 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term166 A s u) = (term166 A s u).
Proof. exact (MK_COMB (@lem3227119 A s u) (@lem3227103 A s u)). Qed.
Lemma lem3227133 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term85 A s u x) = (term85 A s u x).
Proof. exact (eq_refl (term85 A s u x)). Qed.
Lemma lem3227134 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) : (term175 A x s u) = (term175 A x s u).
Proof. exact (MK_COMB (@lem3227133 A s u x) (@lem3227120 A s u)). Qed.
Lemma lem3227135 {A : Type'} (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term175 A x s u) : term175 A x s u.
Proof. exact (EQ_MP (@lem3227134 A x s u) (@lem3227088 A x s u h1)). Qed.
Lemma lem3227160 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) : (term64 A t u x') = (term64 A t u x').
Proof. exact (eq_refl (term64 A t u x')). Qed.
Lemma lem3227171 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A t u x) = (term60 A t u x).
Proof. exact (eq_refl (term60 A t u x)). Qed.
Lemma lem3227172 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term61 A t u) = (term61 A t u).
Proof. exact (fun_ext (fun x : A => @lem3227171 A t u x)). Qed.
Lemma lem3227173 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227174 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term62 A t u) = (term62 A t u).
Proof. exact (MK_COMB (@lem3227173 A) (@lem3227172 A t u)). Qed.
Lemma lem3227175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3227176 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term73 A t u) = (term73 A t u).
Proof. exact (MK_COMB (@lem3227175) (@lem3227174 A t u)). Qed.
Lemma lem3227177 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) : (term115 A t u x') = (term115 A t u x').
Proof. exact (MK_COMB (@lem3227176 A t u) (@lem3227160 A t u x')). Qed.
Lemma lem3227188 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term60 A s t x).
Proof. exact (eq_refl (term60 A s t x)). Qed.
Lemma lem3227189 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term61 A s t).
Proof. exact (fun_ext (fun x : A => @lem3227188 A s t x)). Qed.
Lemma lem3227190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227191 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3227190 A) (@lem3227189 A s t)). Qed.
Lemma lem3227192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3227193 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term73 A s t).
Proof. exact (MK_COMB (@lem3227192) (@lem3227191 A s t)). Qed.
Lemma lem3227194 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) : (term128 A s t u x') = (term128 A s t u x').
Proof. exact (MK_COMB (@lem3227193 A s t) (@lem3227177 A t u x')). Qed.
Lemma lem3227195 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term128 A s t u x'.
Proof. exact (EQ_MP (@lem3227194 A s t u x') (@lem3227089 A s t u x' h1)). Qed.
Lemma lem3227196 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term115 A t u x'.
Proof. exact (proj2 (@lem3227195 A s t u x' h1)). Qed.
Lemma lem3227197 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A s t.
Proof. exact (proj1 (@lem3227195 A s t u x' h1)). Qed.
Lemma lem3227198 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term64 A t u x'.
Proof. exact (proj2 (@lem3227196 A s t u x' h1)). Qed.
Lemma lem3227199 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A t u.
Proof. exact (proj1 (@lem3227196 A s t u x' h1)). Qed.
Lemma lem3227200 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term83 A t u x'.
Proof. exact (h1). Qed.
Lemma lem3227201 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : term87 A t u x'.
Proof. exact (h1). Qed.
Lemma lem3227212 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : term83 A s u x.
Proof. exact (h1). Qed.
Lemma lem3227213 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term166 A s u.
Proof. exact (h1). Qed.
Lemma lem3227217 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term161 A s u.
Proof. exact (proj1 (@lem3227213 A s u h1)). Qed.
Lemma lem3227238 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A t u x) = (term60 A t u x).
Proof. exact (eq_refl (term60 A t u x)). Qed.
Lemma lem3227239 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term61 A t u) = (term61 A t u).
Proof. exact (fun_ext (fun x : A => @lem3227238 A t u x)). Qed.
Lemma lem3227240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227242 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term62 A t u) = (term62 A t u).
Proof. exact (MK_COMB (@lem3227240 A) (@lem3227239 A t u)). Qed.
Lemma lem3227243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A t u.
Proof. exact (EQ_MP (@lem3227242 A t u) (@lem3227199 A s t u x' h1)). Qed.
Lemma lem3227280 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A t u x) = (term60 A t u x).
Proof. exact (eq_refl (term60 A t u x)). Qed.
Lemma lem3227281 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term61 A t u) = (term61 A t u).
Proof. exact (fun_ext (fun x : A => @lem3227280 A t u x)). Qed.
Lemma lem3227282 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227284 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term62 A t u) = (term62 A t u).
Proof. exact (MK_COMB (@lem3227282 A) (@lem3227281 A t u)). Qed.
Lemma lem3227285 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A t u.
Proof. exact (EQ_MP (@lem3227284 A t u) (@lem3227199 A s t u x' h1)). Qed.
Lemma lem3227327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term60 A s t x).
Proof. exact (eq_refl (term60 A s t x)). Qed.
Lemma lem3227328 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term61 A s t).
Proof. exact (fun_ext (fun x : A => @lem3227327 A s t x)). Qed.
Lemma lem3227329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3227329 A) (@lem3227328 A s t)). Qed.
Lemma lem3227332 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A s t.
Proof. exact (EQ_MP (@lem3227331 A s t) (@lem3227197 A s t u x' h1)). Qed.
Lemma lem3227340 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A t u x) = (term60 A t u x).
Proof. exact (eq_refl (term60 A t u x)). Qed.
Lemma lem3227341 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term61 A t u) = (term61 A t u).
Proof. exact (fun_ext (fun x : A => @lem3227340 A t u x)). Qed.
Lemma lem3227342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227344 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term62 A t u) = (term62 A t u).
Proof. exact (MK_COMB (@lem3227342 A) (@lem3227341 A t u)). Qed.
Lemma lem3227345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A t u.
Proof. exact (EQ_MP (@lem3227344 A t u) (@lem3227199 A s t u x' h1)). Qed.
Lemma lem3227369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term60 A s t x).
Proof. exact (eq_refl (term60 A s t x)). Qed.
Lemma lem3227370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term61 A s t).
Proof. exact (fun_ext (fun x : A => @lem3227369 A s t x)). Qed.
Lemma lem3227371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227373 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3227371 A) (@lem3227370 A s t)). Qed.
Lemma lem3227374 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term62 A s t.
Proof. exact (EQ_MP (@lem3227373 A s t) (@lem3227197 A s t u x' h1)). Qed.
Lemma lem3227403 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term151 A s u x) = (term151 A s u x).
Proof. exact (eq_refl (term151 A s u x)). Qed.
Lemma lem3227404 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term149 A s u) = (term149 A s u).
Proof. exact (fun_ext (fun x : A => @lem3227403 A s u x)). Qed.
Lemma lem3227405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3227407 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term161 A s u) = (term161 A s u).
Proof. exact (MK_COMB (@lem3227405 A) (@lem3227404 A s u)). Qed.
Lemma lem3227408 {A : Type'} (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term161 A s u.
Proof. exact (EQ_MP (@lem3227407 A s u) (@lem3227217 A s u h1)). Qed.
Lemma lem3227425 {A : Type'} (_33164 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term154 A t u _33164.
Proof. exact (@lem3227243 A s t u x' h1 _33164). Qed.
Lemma lem3227426 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33164 : A) : (term154 A t u _33164) = (term60 A t u _33164).
Proof. exact (eq_refl (term154 A t u _33164)). Qed.
Lemma lem3227431 {A : Type'} (_33166 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term154 A t u _33166.
Proof. exact (@lem3227285 A s t u x' h1 _33166). Qed.
Lemma lem3227432 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33166 : A) : (term154 A t u _33166) = (term60 A t u _33166).
Proof. exact (eq_refl (term154 A t u _33166)). Qed.
Lemma lem3227440 {A : Type'} (_33169 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term154 A s t _33169.
Proof. exact (@lem3227332 A s t u x' h1 _33169). Qed.
Lemma lem3227441 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33169 : A) : (term154 A s t _33169) = (term60 A s t _33169).
Proof. exact (eq_refl (term154 A s t _33169)). Qed.
Lemma lem3227443 {A : Type'} (_33170 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term154 A t u _33170.
Proof. exact (@lem3227345 A s t u x' h1 _33170). Qed.
Lemma lem3227444 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33170 : A) : (term154 A t u _33170) = (term60 A t u _33170).
Proof. exact (eq_refl (term154 A t u _33170)). Qed.
Lemma lem3227446 {A : Type'} (_33171 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term154 A s t _33171.
Proof. exact (@lem3227374 A s t u x' h1 _33171). Qed.
Lemma lem3227447 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33171 : A) : (term154 A s t _33171) = (term60 A s t _33171).
Proof. exact (eq_refl (term154 A s t _33171)). Qed.
Lemma lem3227452 {A : Type'} (_33173 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term150 A s u _33173.
Proof. exact (@lem3227408 A s u h1 _33173). Qed.
Lemma lem3227453 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_33173 : A) : (term150 A s u _33173) = (term151 A s u _33173).
Proof. exact (eq_refl (term150 A s u _33173)). Qed.
Lemma lem3227469 {A : Type'} (_33164 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term60 A t u _33164.
Proof. exact (EQ_MP (@lem3227426 A t u _33164) (@lem3227425 A _33164 s t u x' h1)). Qed.
Lemma lem3227473 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term179 A u x'.
Proof. exact (proj2 (@lem3227200 A t u x' h1)). Qed.
Lemma lem3227489 {A : Type'} (_33166 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term60 A t u _33166.
Proof. exact (EQ_MP (@lem3227432 A t u _33166) (@lem3227431 A _33166 s t u x' h1)). Qed.
Lemma lem3227493 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term179 A u x'.
Proof. exact (proj2 (@lem3227200 A t u x' h1)). Qed.
Lemma lem3227511 {A : Type'} (_33169 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term60 A s t _33169.
Proof. exact (EQ_MP (@lem3227441 A s t _33169) (@lem3227440 A _33169 s t u x' h1)). Qed.
Lemma lem3227517 {A : Type'} (_33170 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term60 A t u _33170.
Proof. exact (EQ_MP (@lem3227444 A t u _33170) (@lem3227443 A _33170 s t u x' h1)). Qed.
Lemma lem3227525 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : term179 A u x.
Proof. exact (proj2 (@lem3227212 A s u x h1)). Qed.
Lemma lem3227531 {A : Type'} (_33171 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term60 A s t _33171.
Proof. exact (EQ_MP (@lem3227447 A s t _33171) (@lem3227446 A _33171 s t u x' h1)). Qed.
Lemma lem3227539 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : term179 A t x'.
Proof. exact (proj1 (@lem3227201 A t u x' h1)). Qed.
Lemma lem3227547 {A : Type'} (_33173 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term151 A s u _33173.
Proof. exact (EQ_MP (@lem3227453 A s u _33173) (@lem3227452 A _33173 s u h1)). Qed.
Lemma lem3227555 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : t x'.
Proof. exact (proj1 (@lem3227200 A t u x' h1)). Qed.
Lemma lem3227556 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term180 A t x'.
Proof. exact (fun h0 : term179 A t x' => @lem3227555 A t u x' h1). Qed.
Lemma lem3227558 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227559 {A : Type'} (t : A -> Prop) (x' : A) : (term180 A t x') = (t x').
Proof. exact (@lem3227558 (t x')). Qed.
Lemma lem3227560 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : t x'.
Proof. exact (EQ_MP (@lem3227559 A t x') (@lem3227556 A t u x' h1)). Qed.
Lemma lem3227566 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3227567 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : (term60 A t u _33164) = (term151 A u t _33164).
Proof. exact (@lem3227566 (u _33164) (term179 A t _33164)). Qed.
Lemma lem3227573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227574 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : (term182 A t u _33164) = (term183 A u t _33164).
Proof. exact (MK_COMB (@lem3227573) (@lem3227567 A u t _33164)). Qed.
Lemma lem3227580 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : (term151 A u t _33164) = (term151 A u t _33164).
Proof. exact (eq_refl (term151 A u t _33164)). Qed.
Lemma lem3227581 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : ((term60 A t u _33164) = (term151 A u t _33164)) = ((term151 A u t _33164) = (term151 A u t _33164)).
Proof. exact (MK_COMB (@lem3227574 A u t _33164) (@lem3227580 A u t _33164)). Qed.
Lemma lem3227583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3227584 (x : Prop) : (x = x) = True.
Proof. exact (@lem3227583 Prop x). Qed.
Lemma lem3227585 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : ((term151 A u t _33164) = (term151 A u t _33164)) = True.
Proof. exact (@lem3227584 (term151 A u t _33164)). Qed.
Lemma lem3227586 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : ((term60 A t u _33164) = (term151 A u t _33164)) = True.
Proof. exact (TRANS (@lem3227581 A u t _33164) (@lem3227585 A u t _33164)). Qed.
Lemma lem3227587 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : True = ((term60 A t u _33164) = (term151 A u t _33164)).
Proof. exact (SYM (@lem3227586 A u t _33164)). Qed.
Lemma lem3227588 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33164 : A) : (term60 A t u _33164) = (term151 A u t _33164).
Proof. exact (EQ_MP (@lem3227587 A u t _33164) (@lem0)). Qed.
Lemma lem3227589 {A : Type'} (_33164 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term151 A u t _33164.
Proof. exact (EQ_MP (@lem3227588 A u t _33164) (@lem3227469 A _33164 s t u x' h1)). Qed.
Lemma lem3227591 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227592 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33164 : A) : (term151 A u t _33164) = (term185 A t u _33164).
Proof. exact (@lem3227591 (term179 A t _33164) (u _33164)). Qed.
Lemma lem3227594 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227595 {A : Type'} (t : A -> Prop) (_33164 : A) : (term186 A t _33164) = (t _33164).
Proof. exact (@lem3227594 (t _33164)). Qed.
Lemma lem3227596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227597 {A : Type'} (t : A -> Prop) (_33164 : A) : (term187 A t _33164) = (term27 A t _33164).
Proof. exact (MK_COMB (@lem3227596) (@lem3227595 A t _33164)). Qed.
Lemma lem3227598 {A : Type'} (u : A -> Prop) (_33164 : A) : (u _33164) = (u _33164).
Proof. exact (eq_refl (u _33164)). Qed.
Lemma lem3227599 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33164 : A) : (term185 A t u _33164) = (term29 A t u _33164).
Proof. exact (MK_COMB (@lem3227597 A t _33164) (@lem3227598 A u _33164)). Qed.
Lemma lem3227600 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33164 : A) : (term151 A u t _33164) = (term29 A t u _33164).
Proof. exact (TRANS (@lem3227592 A t u _33164) (@lem3227599 A t u _33164)). Qed.
Lemma lem3227603 {A : Type'} (_33164 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33164.
Proof. exact (EQ_MP (@lem3227600 A t u _33164) (@lem3227589 A _33164 s t u x' h1)). Qed.
Lemma lem3227604 {A : Type'} (_33164 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33164.
Proof. exact (@lem3227603 A _33164 s t u x' h1). Qed.
Lemma lem3227605 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u x'.
Proof. exact (@lem3227604 A x' s t u x' h1). Qed.
Lemma lem3227608 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : u x'.
Proof. exact (@lem3227605 A s t u x' h1 (@lem3227560 A t u x' h2)). Qed.
Lemma lem3227609 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : term180 A u x'.
Proof. exact (fun h0 : term179 A u x' => @lem3227608 A s t u x' h1 h2). Qed.
Lemma lem3227611 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227612 {A : Type'} (u : A -> Prop) (x' : A) : (term180 A u x') = (u x').
Proof. exact (@lem3227611 (u x')). Qed.
Lemma lem3227613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : u x'.
Proof. exact (EQ_MP (@lem3227612 A u x') (@lem3227609 A s t u x' h1 h2)). Qed.
Lemma lem3227616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3227618 {A : Type'} (u : A -> Prop) (x' : A) : (term179 A u x') = (term188 A u x').
Proof. exact (@lem3227616 (u x')). Qed.
Lemma lem3227621 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term188 A u x'.
Proof. exact (EQ_MP (@lem3227618 A u x') (@lem3227473 A t u x' h1)). Qed.
Lemma lem3227624 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : False.
Proof. exact (@lem3227621 A t u x' h2 (@lem3227613 A s t u x' h1 h2)). Qed.
Lemma lem3227625 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : term189.
Proof. exact (fun h0 : ~ False => @lem3227624 A s t u x' h1 h2). Qed.
Lemma lem3227627 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227628 : term189 = False.
Proof. exact (@lem3227627 False). Qed.
Lemma lem3227629 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : False.
Proof. exact (EQ_MP (@lem3227628) (@lem3227625 A s t u x' h1 h2)). Qed.
Lemma lem3227631 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : t x'.
Proof. exact (proj1 (@lem3227200 A t u x' h1)). Qed.
Lemma lem3227632 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term180 A t x'.
Proof. exact (fun h0 : term179 A t x' => @lem3227631 A t u x' h1). Qed.
Lemma lem3227634 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227635 {A : Type'} (t : A -> Prop) (x' : A) : (term180 A t x') = (t x').
Proof. exact (@lem3227634 (t x')). Qed.
Lemma lem3227636 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : t x'.
Proof. exact (EQ_MP (@lem3227635 A t x') (@lem3227632 A t u x' h1)). Qed.
Lemma lem3227642 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3227643 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : (term60 A t u _33166) = (term151 A u t _33166).
Proof. exact (@lem3227642 (u _33166) (term179 A t _33166)). Qed.
Lemma lem3227649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227650 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : (term182 A t u _33166) = (term183 A u t _33166).
Proof. exact (MK_COMB (@lem3227649) (@lem3227643 A u t _33166)). Qed.
Lemma lem3227656 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : (term151 A u t _33166) = (term151 A u t _33166).
Proof. exact (eq_refl (term151 A u t _33166)). Qed.
Lemma lem3227657 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : ((term60 A t u _33166) = (term151 A u t _33166)) = ((term151 A u t _33166) = (term151 A u t _33166)).
Proof. exact (MK_COMB (@lem3227650 A u t _33166) (@lem3227656 A u t _33166)). Qed.
Lemma lem3227659 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3227660 (x : Prop) : (x = x) = True.
Proof. exact (@lem3227659 Prop x). Qed.
Lemma lem3227661 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : ((term151 A u t _33166) = (term151 A u t _33166)) = True.
Proof. exact (@lem3227660 (term151 A u t _33166)). Qed.
Lemma lem3227662 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : ((term60 A t u _33166) = (term151 A u t _33166)) = True.
Proof. exact (TRANS (@lem3227657 A u t _33166) (@lem3227661 A u t _33166)). Qed.
Lemma lem3227663 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : True = ((term60 A t u _33166) = (term151 A u t _33166)).
Proof. exact (SYM (@lem3227662 A u t _33166)). Qed.
Lemma lem3227664 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33166 : A) : (term60 A t u _33166) = (term151 A u t _33166).
Proof. exact (EQ_MP (@lem3227663 A u t _33166) (@lem0)). Qed.
Lemma lem3227665 {A : Type'} (_33166 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term151 A u t _33166.
Proof. exact (EQ_MP (@lem3227664 A u t _33166) (@lem3227489 A _33166 s t u x' h1)). Qed.
Lemma lem3227667 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227668 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33166 : A) : (term151 A u t _33166) = (term185 A t u _33166).
Proof. exact (@lem3227667 (term179 A t _33166) (u _33166)). Qed.
Lemma lem3227670 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227671 {A : Type'} (t : A -> Prop) (_33166 : A) : (term186 A t _33166) = (t _33166).
Proof. exact (@lem3227670 (t _33166)). Qed.
Lemma lem3227672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227673 {A : Type'} (t : A -> Prop) (_33166 : A) : (term187 A t _33166) = (term27 A t _33166).
Proof. exact (MK_COMB (@lem3227672) (@lem3227671 A t _33166)). Qed.
Lemma lem3227674 {A : Type'} (u : A -> Prop) (_33166 : A) : (u _33166) = (u _33166).
Proof. exact (eq_refl (u _33166)). Qed.
Lemma lem3227675 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33166 : A) : (term185 A t u _33166) = (term29 A t u _33166).
Proof. exact (MK_COMB (@lem3227673 A t _33166) (@lem3227674 A u _33166)). Qed.
Lemma lem3227676 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33166 : A) : (term151 A u t _33166) = (term29 A t u _33166).
Proof. exact (TRANS (@lem3227668 A t u _33166) (@lem3227675 A t u _33166)). Qed.
Lemma lem3227679 {A : Type'} (_33166 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33166.
Proof. exact (EQ_MP (@lem3227676 A t u _33166) (@lem3227665 A _33166 s t u x' h1)). Qed.
Lemma lem3227680 {A : Type'} (_33166 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33166.
Proof. exact (@lem3227679 A _33166 s t u x' h1). Qed.
Lemma lem3227681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u x'.
Proof. exact (@lem3227680 A x' s t u x' h1). Qed.
Lemma lem3227684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : u x'.
Proof. exact (@lem3227681 A s t u x' h1 (@lem3227636 A t u x' h2)). Qed.
Lemma lem3227685 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : term180 A u x'.
Proof. exact (fun h0 : term179 A u x' => @lem3227684 A s t u x' h1 h2). Qed.
Lemma lem3227687 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227688 {A : Type'} (u : A -> Prop) (x' : A) : (term180 A u x') = (u x').
Proof. exact (@lem3227687 (u x')). Qed.
Lemma lem3227689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : u x'.
Proof. exact (EQ_MP (@lem3227688 A u x') (@lem3227685 A s t u x' h1 h2)). Qed.
Lemma lem3227692 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3227694 {A : Type'} (u : A -> Prop) (x' : A) : (term179 A u x') = (term188 A u x').
Proof. exact (@lem3227692 (u x')). Qed.
Lemma lem3227697 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term83 A t u x') : term188 A u x'.
Proof. exact (EQ_MP (@lem3227694 A u x') (@lem3227493 A t u x' h1)). Qed.
Lemma lem3227700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : False.
Proof. exact (@lem3227697 A t u x' h2 (@lem3227689 A s t u x' h1 h2)). Qed.
Lemma lem3227701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : term189.
Proof. exact (fun h0 : ~ False => @lem3227700 A s t u x' h1 h2). Qed.
Lemma lem3227703 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227704 : term189 = False.
Proof. exact (@lem3227703 False). Qed.
Lemma lem3227705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term83 A t u x') : False.
Proof. exact (EQ_MP (@lem3227704) (@lem3227701 A s t u x' h1 h2)). Qed.
Lemma lem3227707 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : s x.
Proof. exact (proj1 (@lem3227212 A s u x h1)). Qed.
Lemma lem3227708 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : term180 A s x.
Proof. exact (fun h0 : term179 A s x => @lem3227707 A s u x h1). Qed.
Lemma lem3227710 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227711 {A : Type'} (s : A -> Prop) (x : A) : (term180 A s x) = (s x).
Proof. exact (@lem3227710 (s x)). Qed.
Lemma lem3227712 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : s x.
Proof. exact (EQ_MP (@lem3227711 A s x) (@lem3227708 A s u x h1)). Qed.
Lemma lem3227718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3227719 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : (term60 A s t _33169) = (term151 A t s _33169).
Proof. exact (@lem3227718 (t _33169) (term179 A s _33169)). Qed.
Lemma lem3227725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227726 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : (term182 A s t _33169) = (term183 A t s _33169).
Proof. exact (MK_COMB (@lem3227725) (@lem3227719 A t s _33169)). Qed.
Lemma lem3227732 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : (term151 A t s _33169) = (term151 A t s _33169).
Proof. exact (eq_refl (term151 A t s _33169)). Qed.
Lemma lem3227733 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : ((term60 A s t _33169) = (term151 A t s _33169)) = ((term151 A t s _33169) = (term151 A t s _33169)).
Proof. exact (MK_COMB (@lem3227726 A t s _33169) (@lem3227732 A t s _33169)). Qed.
Lemma lem3227735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3227736 (x : Prop) : (x = x) = True.
Proof. exact (@lem3227735 Prop x). Qed.
Lemma lem3227737 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : ((term151 A t s _33169) = (term151 A t s _33169)) = True.
Proof. exact (@lem3227736 (term151 A t s _33169)). Qed.
Lemma lem3227738 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : ((term60 A s t _33169) = (term151 A t s _33169)) = True.
Proof. exact (TRANS (@lem3227733 A t s _33169) (@lem3227737 A t s _33169)). Qed.
Lemma lem3227739 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : True = ((term60 A s t _33169) = (term151 A t s _33169)).
Proof. exact (SYM (@lem3227738 A t s _33169)). Qed.
Lemma lem3227740 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33169 : A) : (term60 A s t _33169) = (term151 A t s _33169).
Proof. exact (EQ_MP (@lem3227739 A t s _33169) (@lem0)). Qed.
Lemma lem3227741 {A : Type'} (_33169 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term151 A t s _33169.
Proof. exact (EQ_MP (@lem3227740 A t s _33169) (@lem3227511 A _33169 s t u x' h1)). Qed.
Lemma lem3227743 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227744 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33169 : A) : (term151 A t s _33169) = (term185 A s t _33169).
Proof. exact (@lem3227743 (term179 A s _33169) (t _33169)). Qed.
Lemma lem3227746 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227747 {A : Type'} (s : A -> Prop) (_33169 : A) : (term186 A s _33169) = (s _33169).
Proof. exact (@lem3227746 (s _33169)). Qed.
Lemma lem3227748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227749 {A : Type'} (s : A -> Prop) (_33169 : A) : (term187 A s _33169) = (term27 A s _33169).
Proof. exact (MK_COMB (@lem3227748) (@lem3227747 A s _33169)). Qed.
Lemma lem3227750 {A : Type'} (t : A -> Prop) (_33169 : A) : (t _33169) = (t _33169).
Proof. exact (eq_refl (t _33169)). Qed.
Lemma lem3227751 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33169 : A) : (term185 A s t _33169) = (term29 A s t _33169).
Proof. exact (MK_COMB (@lem3227749 A s _33169) (@lem3227750 A t _33169)). Qed.
Lemma lem3227752 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33169 : A) : (term151 A t s _33169) = (term29 A s t _33169).
Proof. exact (TRANS (@lem3227744 A s t _33169) (@lem3227751 A s t _33169)). Qed.
Lemma lem3227755 {A : Type'} (_33169 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t _33169.
Proof. exact (EQ_MP (@lem3227752 A s t _33169) (@lem3227741 A _33169 s t u x' h1)). Qed.
Lemma lem3227756 {A : Type'} (_33169 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t _33169.
Proof. exact (@lem3227755 A _33169 s t u x' h1). Qed.
Lemma lem3227757 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t x.
Proof. exact (@lem3227756 A x s t u x' h1). Qed.
Lemma lem3227760 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : t x.
Proof. exact (@lem3227757 A x s t u x' h1 (@lem3227712 A s u x h2)). Qed.
Lemma lem3227761 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : term180 A t x.
Proof. exact (fun h0 : term179 A t x => @lem3227760 A t x' s u x h1 h2). Qed.
Lemma lem3227763 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227764 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3227763 (t x)). Qed.
Lemma lem3227765 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : t x.
Proof. exact (EQ_MP (@lem3227764 A t x) (@lem3227761 A t x' s u x h1 h2)). Qed.
Lemma lem3227771 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3227772 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : (term60 A t u _33170) = (term151 A u t _33170).
Proof. exact (@lem3227771 (u _33170) (term179 A t _33170)). Qed.
Lemma lem3227778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227779 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : (term182 A t u _33170) = (term183 A u t _33170).
Proof. exact (MK_COMB (@lem3227778) (@lem3227772 A u t _33170)). Qed.
Lemma lem3227785 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : (term151 A u t _33170) = (term151 A u t _33170).
Proof. exact (eq_refl (term151 A u t _33170)). Qed.
Lemma lem3227786 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : ((term60 A t u _33170) = (term151 A u t _33170)) = ((term151 A u t _33170) = (term151 A u t _33170)).
Proof. exact (MK_COMB (@lem3227779 A u t _33170) (@lem3227785 A u t _33170)). Qed.
Lemma lem3227788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3227789 (x : Prop) : (x = x) = True.
Proof. exact (@lem3227788 Prop x). Qed.
Lemma lem3227790 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : ((term151 A u t _33170) = (term151 A u t _33170)) = True.
Proof. exact (@lem3227789 (term151 A u t _33170)). Qed.
Lemma lem3227791 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : ((term60 A t u _33170) = (term151 A u t _33170)) = True.
Proof. exact (TRANS (@lem3227786 A u t _33170) (@lem3227790 A u t _33170)). Qed.
Lemma lem3227792 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : True = ((term60 A t u _33170) = (term151 A u t _33170)).
Proof. exact (SYM (@lem3227791 A u t _33170)). Qed.
Lemma lem3227793 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_33170 : A) : (term60 A t u _33170) = (term151 A u t _33170).
Proof. exact (EQ_MP (@lem3227792 A u t _33170) (@lem0)). Qed.
Lemma lem3227794 {A : Type'} (_33170 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term151 A u t _33170.
Proof. exact (EQ_MP (@lem3227793 A u t _33170) (@lem3227517 A _33170 s t u x' h1)). Qed.
Lemma lem3227796 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227797 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33170 : A) : (term151 A u t _33170) = (term185 A t u _33170).
Proof. exact (@lem3227796 (term179 A t _33170) (u _33170)). Qed.
Lemma lem3227799 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227800 {A : Type'} (t : A -> Prop) (_33170 : A) : (term186 A t _33170) = (t _33170).
Proof. exact (@lem3227799 (t _33170)). Qed.
Lemma lem3227801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227802 {A : Type'} (t : A -> Prop) (_33170 : A) : (term187 A t _33170) = (term27 A t _33170).
Proof. exact (MK_COMB (@lem3227801) (@lem3227800 A t _33170)). Qed.
Lemma lem3227803 {A : Type'} (u : A -> Prop) (_33170 : A) : (u _33170) = (u _33170).
Proof. exact (eq_refl (u _33170)). Qed.
Lemma lem3227804 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33170 : A) : (term185 A t u _33170) = (term29 A t u _33170).
Proof. exact (MK_COMB (@lem3227802 A t _33170) (@lem3227803 A u _33170)). Qed.
Lemma lem3227805 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_33170 : A) : (term151 A u t _33170) = (term29 A t u _33170).
Proof. exact (TRANS (@lem3227797 A t u _33170) (@lem3227804 A t u _33170)). Qed.
Lemma lem3227808 {A : Type'} (_33170 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33170.
Proof. exact (EQ_MP (@lem3227805 A t u _33170) (@lem3227794 A _33170 s t u x' h1)). Qed.
Lemma lem3227809 {A : Type'} (_33170 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u _33170.
Proof. exact (@lem3227808 A _33170 s t u x' h1). Qed.
Lemma lem3227810 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A t u x.
Proof. exact (@lem3227809 A x s t u x' h1). Qed.
Lemma lem3227813 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : u x.
Proof. exact (@lem3227810 A x s t u x' h1 (@lem3227765 A t x' s u x h1 h2)). Qed.
Lemma lem3227814 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : term180 A u x.
Proof. exact (fun h0 : term179 A u x => @lem3227813 A t x' s u x h1 h2). Qed.
Lemma lem3227816 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227817 {A : Type'} (u : A -> Prop) (x : A) : (term180 A u x) = (u x).
Proof. exact (@lem3227816 (u x)). Qed.
Lemma lem3227818 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : u x.
Proof. exact (EQ_MP (@lem3227817 A u x) (@lem3227814 A t x' s u x h1 h2)). Qed.
Lemma lem3227821 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3227823 {A : Type'} (u : A -> Prop) (x : A) : (term179 A u x) = (term188 A u x).
Proof. exact (@lem3227821 (u x)). Qed.
Lemma lem3227826 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term83 A s u x) : term188 A u x.
Proof. exact (EQ_MP (@lem3227823 A u x) (@lem3227525 A s u x h1)). Qed.
Lemma lem3227829 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : False.
Proof. exact (@lem3227826 A s u x h2 (@lem3227818 A t x' s u x h1 h2)). Qed.
Lemma lem3227830 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : term189.
Proof. exact (fun h0 : ~ False => @lem3227829 A t x' s u x h1 h2). Qed.
Lemma lem3227832 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227833 : term189 = False.
Proof. exact (@lem3227832 False). Qed.
Lemma lem3227834 {A : Type'} (t : A -> Prop) (x' : A) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term128 A s t u x') (h2 : term83 A s u x) : False.
Proof. exact (EQ_MP (@lem3227833) (@lem3227830 A t x' s u x h1 h2)). Qed.
Lemma lem3227836 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : u x'.
Proof. exact (proj2 (@lem3227201 A t u x' h1)). Qed.
Lemma lem3227837 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : term180 A u x'.
Proof. exact (fun h0 : term179 A u x' => @lem3227836 A t u x' h1). Qed.
Lemma lem3227839 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227840 {A : Type'} (u : A -> Prop) (x' : A) : (term180 A u x') = (u x').
Proof. exact (@lem3227839 (u x')). Qed.
Lemma lem3227841 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : u x'.
Proof. exact (EQ_MP (@lem3227840 A u x') (@lem3227837 A t u x' h1)). Qed.
Lemma lem3227843 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227844 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33173 : A) : (term151 A s u _33173) = (term185 A u s _33173).
Proof. exact (@lem3227843 (term179 A u _33173) (s _33173)). Qed.
Lemma lem3227846 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227847 {A : Type'} (u : A -> Prop) (_33173 : A) : (term186 A u _33173) = (u _33173).
Proof. exact (@lem3227846 (u _33173)). Qed.
Lemma lem3227848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227849 {A : Type'} (u : A -> Prop) (_33173 : A) : (term187 A u _33173) = (term27 A u _33173).
Proof. exact (MK_COMB (@lem3227848) (@lem3227847 A u _33173)). Qed.
Lemma lem3227850 {A : Type'} (s : A -> Prop) (_33173 : A) : (s _33173) = (s _33173).
Proof. exact (eq_refl (s _33173)). Qed.
Lemma lem3227851 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33173 : A) : (term185 A u s _33173) = (term29 A u s _33173).
Proof. exact (MK_COMB (@lem3227849 A u _33173) (@lem3227850 A s _33173)). Qed.
Lemma lem3227852 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_33173 : A) : (term151 A s u _33173) = (term29 A u s _33173).
Proof. exact (TRANS (@lem3227844 A u s _33173) (@lem3227851 A u s _33173)). Qed.
Lemma lem3227855 {A : Type'} (_33173 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term29 A u s _33173.
Proof. exact (EQ_MP (@lem3227852 A u s _33173) (@lem3227547 A _33173 s u h1)). Qed.
Lemma lem3227856 {A : Type'} (_33173 : A) (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term29 A u s _33173.
Proof. exact (@lem3227855 A _33173 s u h1). Qed.
Lemma lem3227857 {A : Type'} (x' : A) (s : A -> Prop) (u : A -> Prop) (h1 : term166 A s u) : term29 A u s x'.
Proof. exact (@lem3227856 A x' s u h1). Qed.
Lemma lem3227860 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term166 A s u) (h2 : term87 A t u x') : s x'.
Proof. exact (@lem3227857 A x' s u h1 (@lem3227841 A t u x' h2)). Qed.
Lemma lem3227861 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term166 A s u) (h2 : term87 A t u x') : term180 A s x'.
Proof. exact (fun h0 : term179 A s x' => @lem3227860 A s t u x' h1 h2). Qed.
Lemma lem3227863 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227864 {A : Type'} (s : A -> Prop) (x' : A) : (term180 A s x') = (s x').
Proof. exact (@lem3227863 (s x')). Qed.
Lemma lem3227865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term166 A s u) (h2 : term87 A t u x') : s x'.
Proof. exact (EQ_MP (@lem3227864 A s x') (@lem3227861 A s t u x' h1 h2)). Qed.
Lemma lem3227871 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3227872 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : (term60 A s t _33171) = (term151 A t s _33171).
Proof. exact (@lem3227871 (t _33171) (term179 A s _33171)). Qed.
Lemma lem3227878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3227879 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : (term182 A s t _33171) = (term183 A t s _33171).
Proof. exact (MK_COMB (@lem3227878) (@lem3227872 A t s _33171)). Qed.
Lemma lem3227885 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : (term151 A t s _33171) = (term151 A t s _33171).
Proof. exact (eq_refl (term151 A t s _33171)). Qed.
Lemma lem3227886 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : ((term60 A s t _33171) = (term151 A t s _33171)) = ((term151 A t s _33171) = (term151 A t s _33171)).
Proof. exact (MK_COMB (@lem3227879 A t s _33171) (@lem3227885 A t s _33171)). Qed.
Lemma lem3227888 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3227889 (x : Prop) : (x = x) = True.
Proof. exact (@lem3227888 Prop x). Qed.
Lemma lem3227890 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : ((term151 A t s _33171) = (term151 A t s _33171)) = True.
Proof. exact (@lem3227889 (term151 A t s _33171)). Qed.
Lemma lem3227891 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : ((term60 A s t _33171) = (term151 A t s _33171)) = True.
Proof. exact (TRANS (@lem3227886 A t s _33171) (@lem3227890 A t s _33171)). Qed.
Lemma lem3227892 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : True = ((term60 A s t _33171) = (term151 A t s _33171)).
Proof. exact (SYM (@lem3227891 A t s _33171)). Qed.
Lemma lem3227893 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33171 : A) : (term60 A s t _33171) = (term151 A t s _33171).
Proof. exact (EQ_MP (@lem3227892 A t s _33171) (@lem0)). Qed.
Lemma lem3227894 {A : Type'} (_33171 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term151 A t s _33171.
Proof. exact (EQ_MP (@lem3227893 A t s _33171) (@lem3227531 A _33171 s t u x' h1)). Qed.
Lemma lem3227896 (b : Prop) (a : Prop) : (a \/ b) = (term184 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3227897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33171 : A) : (term151 A t s _33171) = (term185 A s t _33171).
Proof. exact (@lem3227896 (term179 A s _33171) (t _33171)). Qed.
Lemma lem3227899 (a : Prop) : (term57 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3227900 {A : Type'} (s : A -> Prop) (_33171 : A) : (term186 A s _33171) = (s _33171).
Proof. exact (@lem3227899 (s _33171)). Qed.
Lemma lem3227901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3227902 {A : Type'} (s : A -> Prop) (_33171 : A) : (term187 A s _33171) = (term27 A s _33171).
Proof. exact (MK_COMB (@lem3227901) (@lem3227900 A s _33171)). Qed.
Lemma lem3227903 {A : Type'} (t : A -> Prop) (_33171 : A) : (t _33171) = (t _33171).
Proof. exact (eq_refl (t _33171)). Qed.
Lemma lem3227904 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33171 : A) : (term185 A s t _33171) = (term29 A s t _33171).
Proof. exact (MK_COMB (@lem3227902 A s _33171) (@lem3227903 A t _33171)). Qed.
Lemma lem3227905 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33171 : A) : (term151 A t s _33171) = (term29 A s t _33171).
Proof. exact (TRANS (@lem3227897 A s t _33171) (@lem3227904 A s t _33171)). Qed.
Lemma lem3227908 {A : Type'} (_33171 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t _33171.
Proof. exact (EQ_MP (@lem3227905 A s t _33171) (@lem3227894 A _33171 s t u x' h1)). Qed.
Lemma lem3227909 {A : Type'} (_33171 : A) (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t _33171.
Proof. exact (@lem3227908 A _33171 s t u x' h1). Qed.
Lemma lem3227910 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') : term29 A s t x'.
Proof. exact (@lem3227909 A x' s t u x' h1). Qed.
Lemma lem3227913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : t x'.
Proof. exact (@lem3227910 A s t u x' h1 (@lem3227865 A s t u x' h2 h3)). Qed.
Lemma lem3227914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : term180 A t x'.
Proof. exact (fun h0 : term179 A t x' => @lem3227913 A s t u x' h1 h2 h3). Qed.
Lemma lem3227916 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227917 {A : Type'} (t : A -> Prop) (x' : A) : (term180 A t x') = (t x').
Proof. exact (@lem3227916 (t x')). Qed.
Lemma lem3227918 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : t x'.
Proof. exact (EQ_MP (@lem3227917 A t x') (@lem3227914 A s t u x' h1 h2 h3)). Qed.
Lemma lem3227921 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3227923 {A : Type'} (t : A -> Prop) (x' : A) : (term179 A t x') = (term188 A t x').
Proof. exact (@lem3227921 (t x')). Qed.
Lemma lem3227926 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term87 A t u x') : term188 A t x'.
Proof. exact (EQ_MP (@lem3227923 A t x') (@lem3227539 A t u x' h1)). Qed.
Lemma lem3227929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : False.
Proof. exact (@lem3227926 A t u x' h3 (@lem3227918 A s t u x' h1 h2 h3)). Qed.
Lemma lem3227930 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : term189.
Proof. exact (fun h0 : ~ False => @lem3227929 A s t u x' h1 h2 h3). Qed.
Lemma lem3227932 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3227933 : term189 = False.
Proof. exact (@lem3227932 False). Qed.
Lemma lem3227934 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x' : A) (h1 : term128 A s t u x') (h2 : term166 A s u) (h3 : term87 A t u x') : False.
Proof. exact (EQ_MP (@lem3227933) (@lem3227930 A s t u x' h1 h2 h3)). Qed.
Lemma lem3227935 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term87 A t u x') (h3 : term175 A x s u) : False.
Proof. exact (or_elim (@lem3227135 A x s u h3) (fun h0 : term83 A s u x => @lem3227834 A t x' s u x h1 h0) (fun h0 : term166 A s u => @lem3227934 A s t u x' h1 h0 h2)). Qed.
Lemma lem3227936 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term83 A t u x') (h3 : term175 A x s u) : False.
Proof. exact (or_elim (@lem3227135 A x s u h3) (fun h0 : term83 A s u x => @lem3227629 A s t u x' h1 h2) (fun h0 : term166 A s u => @lem3227705 A s t u x' h1 h2)). Qed.
Lemma lem3227937 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term175 A x s u) : False.
Proof. exact (or_elim (@lem3227198 A s t u x' h1) (fun h0 : term83 A t u x' => @lem3227936 A t x' x s u h1 h0 h2) (fun h0 : term87 A t u x' => @lem3227935 A t x' x s u h1 h0 h2)). Qed.
Lemma lem3227938 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term175 A x s u) : (term128 A s t u x') = False.
Proof. exact (prop_ext (fun h3 : term128 A s t u x' => @lem3227937 A t x' x s u h1 h2) (fun h3 : False => @lem3227195 A s t u x' h1)). Qed.
Lemma lem3227939 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term175 A x s u) : False.
Proof. exact (EQ_MP (@lem3227938 A t x' x s u h1 h2) (@lem3227195 A s t u x' h1)). Qed.
Lemma lem3227940 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term175 A x s u) : (term175 A x s u) = False.
Proof. exact (prop_ext (fun h3 : term175 A x s u => @lem3227939 A t x' x s u h1 h2) (fun h3 : False => @lem3227135 A x s u h2)). Qed.
Lemma lem3227941 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term128 A s t u x') (h2 : term175 A x s u) : False.
Proof. exact (EQ_MP (@lem3227940 A t x' x s u h1 h2) (@lem3227135 A x s u h2)). Qed.
Lemma lem3227942 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) (h1 : term41 A s t u) (h2 : term175 A x s u) : False.
Proof. exact (ex_elim (@lem3226901 A s t u h1) (fun x' : A => fun h0 : term130 A s t u x' => @lem3227941 A t x' x s u h0 h2)). Qed.
Lemma lem3227943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term59 A s u) (h2 : term41 A s t u) : False.
Proof. exact (ex_elim (@lem3227087 A s u h1) (fun x : A => fun h0 : term177 A s u x => @lem3227942 A t x s u h2 h0)). Qed.
Lemma lem3227944 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term59 A s u) (h2 : term41 A s t u) : (term59 A s u) = False.
Proof. exact (prop_ext (fun h3 : term59 A s u => @lem3227943 A s t u h1 h2) (fun h3 : False => @lem3226619 A s u h1)). Qed.
Lemma lem3227945 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term59 A s u) (h2 : term41 A s t u) : False.
Proof. exact (EQ_MP (@lem3227944 A s t u h1 h2) (@lem3226619 A s u h1)). Qed.
Lemma lem3227946 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term41 A s t u) : term58 A s u.
Proof. exact (fun h0 : term59 A s u => @lem3227945 A s t u h0 h1). Qed.
Lemma lem3227947 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (h1 : term41 A s t u) : term40 A s u.
Proof. exact (EQ_MP (@lem3226618 A s u) (@lem3227946 A s t u h1)). Qed.
Lemma lem3227948 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term43 A t s u.
Proof. exact (fun h0 : term41 A s t u => @lem3227947 A s t u h0). Qed.
Lemma lem3227953 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term45 A t s.
Proof. exact (fun u : A -> Prop => @lem3227948 A t s u). Qed.
Lemma lem3227958 {A : Type'} (s : A -> Prop) : term47 A s.
Proof. exact (fun t : A -> Prop => @lem3227953 A t s). Qed.
Lemma lem3227963 {A : Type'} : term49 A.
Proof. exact (fun s : A -> Prop => @lem3227958 A s). Qed.
Lemma lem3227964 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3226613 A) (@lem3227963 A)). Qed.
Lemma lem3227966 {A : Type'} : term51 A.
Proof. exact (@lem3226425 A (@lem3227964 A)). Qed.
Lemma lem3227967 {A : Type'} (h1 : term52 A) : False.
Proof. exact (@lem3227966 A (@lem3226409 A h1)). Qed.
Lemma lem3227968 {A : Type'} (h1 : term52 A) : (term52 A) = False.
Proof. exact (prop_ext (fun h2 : term52 A => @lem3227967 A h1) (fun h2 : False => @lem3226409 A h1)). Qed.
Lemma lem3227969 {A : Type'} (h1 : term52 A) : False.
Proof. exact (EQ_MP (@lem3227968 A h1) (@lem3226409 A h1)). Qed.
Lemma lem3227970 {A : Type'} : term51 A.
Proof. exact (fun h0 : term52 A => @lem3227969 A h0). Qed.
Lemma lem3227971 {A : Type'} : term49 A.
Proof. exact (EQ_MP (@lem3226408 A) (@lem3227970 A)). Qed.
Lemma lem3227972 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3226404 A) (@lem3227971 A)). Qed.
Lemma lem3227973 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3226208 A) (@lem3227972 A)). Qed.
