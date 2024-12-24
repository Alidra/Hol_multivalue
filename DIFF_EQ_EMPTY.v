Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_EQ_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1857_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3270133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3270134 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3270133 A s t). Qed.
Lemma lem3270135 {A : Type'} (s : A -> Prop) : ((@DIFF A s s) = (@EMPTY A)) = (term1 A s).
Proof. exact (@lem3270134 A (@DIFF A s s) (@EMPTY A)). Qed.
Lemma lem3270144 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3270135 A s)). Qed.
Lemma lem3270145 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3270146 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3270145 A) (@lem3270144 A)). Qed.
Lemma lem3270151 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3270146 A)). Qed.
Lemma lem3270163 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270164 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term6 A x s t) = (term7 A s x t).
Proof. exact (@lem3270163 A s x t). Qed.
Lemma lem3270165 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (@lem3270164 A s x s). Qed.
Lemma lem3270169 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3270169 A P x). Qed.
Lemma lem3270171 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3270170 A s x). Qed.
Lemma lem3270172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270173 {A : Type'} (s : A -> Prop) (x : A) : (term10 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3270172) (@lem3270171 A s x)). Qed.
Lemma lem3270175 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3270175 A P x). Qed.
Lemma lem3270177 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3270176 A s x). Qed.
Lemma lem3270178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3270179 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem3270178) (@lem3270177 A s x)). Qed.
Lemma lem3270180 {A : Type'} (s : A -> Prop) (x : A) : (term9 A x s) = (term14 A s x).
Proof. exact (MK_COMB (@lem3270173 A s x) (@lem3270179 A s x)). Qed.
Lemma lem3270183 {A : Type'} (s : A -> Prop) (x : A) : (term8 A x s) = (term14 A s x).
Proof. exact (TRANS (@lem3270165 A x s) (@lem3270180 A s x)). Qed.
Lemma lem3270184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3270185 {A : Type'} (s : A -> Prop) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (MK_COMB (@lem3270184) (@lem3270183 A s x)). Qed.
Lemma lem3270187 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3270188 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3270187 A x). Qed.
Lemma lem3270189 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = ((term14 A s x) = False).
Proof. exact (MK_COMB (@lem3270185 A s x) (@lem3270188 A x)). Qed.
Lemma lem3270191 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3270192 {A : Type'} (s : A -> Prop) (x : A) : ((term14 A s x) = False) = (term17 A s x).
Proof. exact (@lem3270191 (term14 A s x)). Qed.
Lemma lem3270195 {A : Type'} (s : A -> Prop) (x : A) : ((term8 A x s) = (@IN A x (@EMPTY A))) = (term17 A s x).
Proof. exact (TRANS (@lem3270189 A s x) (@lem3270192 A s x)). Qed.
Lemma lem3270196 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (fun_ext (fun x : A => @lem3270195 A s x)). Qed.
Lemma lem3270197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3270198 {A : Type'} (s : A -> Prop) : (term1 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3270197 A) (@lem3270196 A s)). Qed.
Lemma lem3270203 {A : Type'} : (term3 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3270198 A s)). Qed.
Lemma lem3270204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3270205 {A : Type'} : (term5 A) = (term22 A).
Proof. exact (MK_COMB (@lem3270204 A) (@lem3270203 A)). Qed.
Lemma lem3270210 {A : Type'} : (term22 A) = (term5 A).
Proof. exact (SYM (@lem3270205 A)). Qed.
Lemma lem3270212 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3270213 {A : Type'} : (term22 A) = (term24 A).
Proof. exact (@lem3270212 (term22 A)). Qed.
Lemma lem3270214 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (SYM (@lem3270213 A)). Qed.
Lemma lem3270215 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3270218 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem3270219 {A : Type'} : term26 A.
Proof. exact (fun h0 : term24 A => @lem3270218 A h0). Qed.
Lemma lem3270220 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3270221 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem3270222 {A : Type'} (h1 : term24 A) (h2 : term26 A) : term24 A.
Proof. exact (@lem3270220 A h2 (@lem3270221 A h1)). Qed.
Lemma lem3270223 {A : Type'} (h1 : term24 A) : term27 A.
Proof. exact (fun h0 : term26 A => @lem3270222 A h1 h0). Qed.
Lemma lem3270224 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3270225 {A : Type'} (h1 : term24 A) (h2 : term26 A) : term24 A.
Proof. exact (@lem3270223 A h1 (@lem3270224 A h2)). Qed.
Lemma lem3270226 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (fun h0 : term24 A => @lem3270225 A h0 h1). Qed.
Lemma lem3270227 {A : Type'} : term28 A.
Proof. exact (fun h0 : term26 A => @lem3270226 A h0). Qed.
Lemma lem3270230 {A : Type'} : term26 A.
Proof. exact (@lem3270227 A (@lem3270219 A)). Qed.
Lemma lem3270231 {A : Type'} : term26 A.
Proof. exact (@lem3270230 A). Qed.
Lemma lem3270233 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3270234 {A : Type'} : (term24 A) = (term29 A).
Proof. exact (@lem3270233 (term25 A)). Qed.
Lemma lem3270236 (t : Prop) : (term30 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3270237 {A : Type'} : (term29 A) = (term22 A).
Proof. exact (@lem3270236 (term22 A)). Qed.
Lemma lem3270252 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (TRANS (@lem3270234 A) (@lem3270237 A)). Qed.
Lemma lem3270261 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = (term17 A s x).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3270262 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (fun_ext (fun x : A => @lem3270261 A s x)). Qed.
Lemma lem3270263 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3270264 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3270263 A) (@lem3270262 A s)). Qed.
Lemma lem3270265 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3270264 A s)). Qed.
Lemma lem3270266 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3270267 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3270266 A) (@lem3270265 A)). Qed.
Lemma lem3270284 {A : Type'} : (term24 A) = (term22 A).
Proof. exact (TRANS (@lem3270252 A) (@lem3270267 A)). Qed.
Lemma lem3270285 {A : Type'} : (term22 A) = (term24 A).
Proof. exact (SYM (@lem3270284 A)). Qed.
Lemma lem3270296 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term14 A s x.
Proof. exact (h1). Qed.
Lemma lem3270308 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term14 A s x.
Proof. exact (h1). Qed.
Lemma lem3270322 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term13 A s x.
Proof. exact (proj2 (@lem3270308 A s x h1)). Qed.
Lemma lem3270324 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : s x.
Proof. exact (proj1 (@lem3270308 A s x h1)). Qed.
Lemma lem3270325 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term31 A s x.
Proof. exact (fun h0 : term13 A s x => @lem3270324 A s x h1). Qed.
Lemma lem3270327 (p : Prop) : (term32 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270328 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (s x).
Proof. exact (@lem3270327 (s x)). Qed.
Lemma lem3270329 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : s x.
Proof. exact (EQ_MP (@lem3270328 A s x) (@lem3270325 A s x h1)). Qed.
Lemma lem3270332 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3270334 {A : Type'} (s : A -> Prop) (x : A) : (term13 A s x) = (term33 A s x).
Proof. exact (@lem3270332 (s x)). Qed.
Lemma lem3270337 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term33 A s x.
Proof. exact (EQ_MP (@lem3270334 A s x) (@lem3270322 A s x h1)). Qed.
Lemma lem3270340 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : False.
Proof. exact (@lem3270337 A s x h1 (@lem3270329 A s x h1)). Qed.
Lemma lem3270341 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : term34.
Proof. exact (fun h0 : ~ False => @lem3270340 A s x h1). Qed.
Lemma lem3270343 (p : Prop) : (term32 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3270344 : term34 = False.
Proof. exact (@lem3270343 False). Qed.
Lemma lem3270345 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : False.
Proof. exact (EQ_MP (@lem3270344) (@lem3270341 A s x h1)). Qed.
Lemma lem3270346 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : (term14 A s x) = False.
Proof. exact (prop_ext (fun h2 : term14 A s x => @lem3270345 A s x h1) (fun h2 : False => @lem3270308 A s x h1)). Qed.
Lemma lem3270347 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : False.
Proof. exact (EQ_MP (@lem3270346 A s x h1) (@lem3270308 A s x h1)). Qed.
Lemma lem3270348 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : (term14 A s x) = False.
Proof. exact (prop_ext (fun h2 : term14 A s x => @lem3270347 A s x h1) (fun h2 : False => @lem3270296 A s x h1)). Qed.
Lemma lem3270349 {A : Type'} (s : A -> Prop) (x : A) (h1 : term14 A s x) : False.
Proof. exact (EQ_MP (@lem3270348 A s x h1) (@lem3270296 A s x h1)). Qed.
Lemma lem3270350 {A : Type'} (s : A -> Prop) (x : A) : term35 A s x.
Proof. exact (fun h0 : term14 A s x => @lem3270349 A s x h0). Qed.
Lemma lem3270351 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term17 A s x).
Proof. exact (@lem69 (term14 A s x)). Qed.
Lemma lem3270352 {A : Type'} (s : A -> Prop) (x : A) : term17 A s x.
Proof. exact (EQ_MP (@lem3270351 A s x) (@lem3270350 A s x)). Qed.
Lemma lem3270357 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (fun x : A => @lem3270352 A s x). Qed.
Lemma lem3270362 {A : Type'} : term22 A.
Proof. exact (fun s : A -> Prop => @lem3270357 A s). Qed.
Lemma lem3270363 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3270285 A) (@lem3270362 A)). Qed.
Lemma lem3270365 {A : Type'} : term24 A.
Proof. exact (@lem3270231 A (@lem3270363 A)). Qed.
Lemma lem3270366 {A : Type'} (h1 : term25 A) : False.
Proof. exact (@lem3270365 A (@lem3270215 A h1)). Qed.
Lemma lem3270367 {A : Type'} (h1 : term25 A) : (term25 A) = False.
Proof. exact (prop_ext (fun h2 : term25 A => @lem3270366 A h1) (fun h2 : False => @lem3270215 A h1)). Qed.
Lemma lem3270368 {A : Type'} (h1 : term25 A) : False.
Proof. exact (EQ_MP (@lem3270367 A h1) (@lem3270215 A h1)). Qed.
Lemma lem3270369 {A : Type'} : term24 A.
Proof. exact (fun h0 : term25 A => @lem3270368 A h0). Qed.
Lemma lem3270370 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3270214 A) (@lem3270369 A)). Qed.
Lemma lem3270371 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3270210 A) (@lem3270370 A)). Qed.
Lemma lem3270372 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3270151 A) (@lem3270371 A)). Qed.
