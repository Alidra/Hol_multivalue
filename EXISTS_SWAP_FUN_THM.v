Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SWAP_FUN_THM_term_abbrevs.
Require Import ETA_AX_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem55167 {A B C : Type'} (P : type443 A B C) (h1 : term0 A B C P) : term0 A B C P.
Proof. exact (h1). Qed.
Lemma lem55168 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : P f.
Proof. exact (h1). Qed.
Lemma lem55169 {A B C : Type'} (P : type443 A B C) (h1 : term1 A B C P) : term1 A B C P.
Proof. exact (h1). Qed.
Lemma lem55170 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : term2 A B C P f.
Proof. exact (h1). Qed.
Lemma lem55171 {A B : Type'} (t : A -> B) : term3 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem55172 {A B : Type'} (t : A -> B) : (term3 A B t) = ((term4 A B t) = t).
Proof. exact (eq_refl (term3 A B t)). Qed.
Lemma lem55173 {A B : Type'} (t : A -> B) : (term4 A B t) = t.
Proof. exact (EQ_MP (@lem55172 A B t) (@lem55171 A B t)). Qed.
Lemma lem55174 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (P f) = ((P f) = True).
Proof. exact (@lem7 (P f)). Qed.
Lemma lem55177 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55178 {A B C : Type'} (f : type1469 A B C) (y : B) : (term6 A B C f y) = (f y).
Proof. exact (@lem55177 B (A -> C) f y). Qed.
Lemma lem55179 {A B C : Type'} (f : type1412 A B C) (b : B) : (term7 A B C f b) = (term8 A B C f b).
Proof. exact (@lem55178 A B C (term9 A B C f) b). Qed.
Lemma lem55180 {A B C : Type'} (f : type1412 A B C) (b : B) : (term8 A B C f b) = (term10 A B C f b).
Proof. exact (eq_refl (term8 A B C f b)). Qed.
Lemma lem55181 {A B C : Type'} (f : type1412 A B C) : (term11 A B C f) = (term9 A B C f).
Proof. exact (fun_ext (fun b : B => @lem55180 A B C f b)). Qed.
Lemma lem55182 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem55183 {A B C : Type'} (f : type1412 A B C) (b : B) : (term7 A B C f b) = (term8 A B C f b).
Proof. exact (MK_COMB (@lem55181 A B C f) (@lem55182 B b)). Qed.
Lemma lem55184 {A C : Type'} : (@eq (A -> C)) = (@eq (A -> C)).
Proof. exact (eq_refl (@eq (A -> C))). Qed.
Lemma lem55185 {A B C : Type'} (f : type1412 A B C) (b : B) : (term12 A B C f b) = (term13 A B C f b).
Proof. exact (MK_COMB (@lem55184 A C) (@lem55183 A B C f b)). Qed.
Lemma lem55186 {A B C : Type'} (f : type1412 A B C) (b : B) : (term8 A B C f b) = (term10 A B C f b).
Proof. exact (eq_refl (term8 A B C f b)). Qed.
Lemma lem55187 {A B C : Type'} (f : type1412 A B C) (b : B) : ((term7 A B C f b) = (term8 A B C f b)) = ((term8 A B C f b) = (term10 A B C f b)).
Proof. exact (MK_COMB (@lem55185 A B C f b) (@lem55186 A B C f b)). Qed.
Lemma lem55188 {A B C : Type'} (f : type1412 A B C) (b : B) : (term8 A B C f b) = (term10 A B C f b).
Proof. exact (EQ_MP (@lem55187 A B C f b) (@lem55179 A B C f b)). Qed.
Lemma lem55189 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem55190 {A B C : Type'} (f : type1412 A B C) (b : B) (a : A) : (term14 A B C f b a) = (term15 A B C f b a).
Proof. exact (MK_COMB (@lem55188 A B C f b) (@lem55189 A a)). Qed.
Lemma lem55192 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55193 {A C : Type'} (f : A -> C) (y : A) : (term5 A C f y) = (f y).
Proof. exact (@lem55192 A C f y). Qed.
Lemma lem55194 {A B C : Type'} (f : type1412 A B C) (b : B) (a : A) : (term16 A B C f b a) = (term15 A B C f b a).
Proof. exact (@lem55193 A C (term10 A B C f b) a). Qed.
Lemma lem55195 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term15 A B C f b a) = (f a b).
Proof. exact (eq_refl (term15 A B C f b a)). Qed.
Lemma lem55196 {A B C : Type'} (f : type1412 A B C) (b : B) : (term17 A B C f b) = (term10 A B C f b).
Proof. exact (fun_ext (fun a : A => @lem55195 A B C f a b)). Qed.
Lemma lem55197 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem55198 {A B C : Type'} (f : type1412 A B C) (b : B) (a : A) : (term16 A B C f b a) = (term15 A B C f b a).
Proof. exact (MK_COMB (@lem55196 A B C f b) (@lem55197 A a)). Qed.
Lemma lem55199 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem55200 {A B C : Type'} (f : type1412 A B C) (b : B) (a : A) : (term18 A B C f b a) = (term19 A B C f b a).
Proof. exact (MK_COMB (@lem55199 C) (@lem55198 A B C f b a)). Qed.
Lemma lem55201 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term15 A B C f b a) = (f a b).
Proof. exact (eq_refl (term15 A B C f b a)). Qed.
Lemma lem55202 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : ((term16 A B C f b a) = (term15 A B C f b a)) = ((term15 A B C f b a) = (f a b)).
Proof. exact (MK_COMB (@lem55200 A B C f b a) (@lem55201 A B C f a b)). Qed.
Lemma lem55203 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term15 A B C f b a) = (f a b).
Proof. exact (EQ_MP (@lem55202 A B C f a b) (@lem55194 A B C f b a)). Qed.
Lemma lem55204 {A B C : Type'} (f : type1412 A B C) (a : A) (b : B) : (term14 A B C f b a) = (f a b).
Proof. exact (TRANS (@lem55190 A B C f b a) (@lem55203 A B C f a b)). Qed.
Lemma lem55205 {A B C : Type'} (f : type1412 A B C) (a : A) : (term20 A B C f a) = (term21 A B C f a).
Proof. exact (fun_ext (fun b : B => @lem55204 A B C f a b)). Qed.
Lemma lem55206 {B C : Type'} (t : B -> C) : (term4 B C t) = t.
Proof. exact (@lem55173 B C t). Qed.
Lemma lem55207 {A B C : Type'} (f : type1412 A B C) (a : A) : (term21 A B C f a) = (f a).
Proof. exact (@lem55206 B C (f a)). Qed.
Lemma lem55208 {A B C : Type'} (f : type1412 A B C) (a : A) : (term20 A B C f a) = (f a).
Proof. exact (TRANS (@lem55205 A B C f a) (@lem55207 A B C f a)). Qed.
Lemma lem55209 {A B C : Type'} (f : type1412 A B C) : (term22 A B C f) = (term23 A B C f).
Proof. exact (fun_ext (fun a : A => @lem55208 A B C f a)). Qed.
Lemma lem55210 {A B C : Type'} (t : type1412 A B C) : (term23 A B C t) = t.
Proof. exact (@lem55173 A (B -> C) t). Qed.
Lemma lem55211 {A B C : Type'} (f : type1412 A B C) : (term23 A B C f) = f.
Proof. exact (@lem55210 A B C f). Qed.
Lemma lem55212 {A B C : Type'} (f : type1412 A B C) : (term22 A B C f) = f.
Proof. exact (TRANS (@lem55209 A B C f) (@lem55211 A B C f)). Qed.
Lemma lem55213 {A B C : Type'} (P : type443 A B C) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem55214 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) : (term24 A B C P f) = (P f).
Proof. exact (MK_COMB (@lem55213 A B C P) (@lem55212 A B C f)). Qed.
Lemma lem55216 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : (P f) = True.
Proof. exact (EQ_MP (@lem55174 A B C P f) (@lem55168 A B C P f h1)). Qed.
Lemma lem55217 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : (term24 A B C P f) = True.
Proof. exact (TRANS (@lem55214 A B C P f) (@lem55216 A B C P f h1)). Qed.
Lemma lem55218 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : True = (term24 A B C P f).
Proof. exact (SYM (@lem55217 A B C P f h1)). Qed.
Lemma lem55219 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : term24 A B C P f.
Proof. exact (EQ_MP (@lem55218 A B C P f h1) (@lem0)). Qed.
Lemma lem55223 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) : (term2 A B C P f) = ((term2 A B C P f) = True).
Proof. exact (@lem7 (term2 A B C P f)). Qed.
Lemma lem55226 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : (term2 A B C P f) = True.
Proof. exact (EQ_MP (@lem55223 A B C P f) (@lem55170 A B C P f h1)). Qed.
Lemma lem55227 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : (term2 A B C P f) = True.
Proof. exact (@lem55226 A B C P f h1). Qed.
Lemma lem55228 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : True = (term2 A B C P f).
Proof. exact (SYM (@lem55227 A B C P f h1)). Qed.
Lemma lem55229 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : term2 A B C P f.
Proof. exact (EQ_MP (@lem55228 A B C P f h1) (@lem0)). Qed.
Lemma lem55230 {A B C : Type'} (P : type443 A B C) (f : type1469 A B C) (h1 : term2 A B C P f) : term0 A B C P.
Proof. exact (ex_intro (term25 A B C P) (term26 A B C f) (@lem55229 A B C P f h1)). Qed.
Lemma lem55231 {A B C : Type'} (P : type443 A B C) (h1 : term1 A B C P) : term0 A B C P.
Proof. exact (ex_elim (@lem55169 A B C P h1) (fun f : type1469 A B C => fun h0 : term27 A B C P f => @lem55230 A B C P f h0)). Qed.
Lemma lem55232 {A B C : Type'} (P : type443 A B C) : term28 A B C P.
Proof. exact (fun h0 : term1 A B C P => @lem55231 A B C P h0). Qed.
Lemma lem55233 {A B C : Type'} (P : type443 A B C) (f : type1412 A B C) (h1 : P f) : term1 A B C P.
Proof. exact (ex_intro (term27 A B C P) (term9 A B C f) (@lem55219 A B C P f h1)). Qed.
Lemma lem55234 {A B C : Type'} (P : type443 A B C) (h1 : term0 A B C P) : term1 A B C P.
Proof. exact (ex_elim (@lem55167 A B C P h1) (fun f : type1412 A B C => fun h0 : term25 A B C P f => @lem55233 A B C P f h0)). Qed.
Lemma lem55235 {A B C : Type'} (P : type443 A B C) : term29 A B C P.
Proof. exact (fun h0 : term0 A B C P => @lem55234 A B C P h0). Qed.
Lemma lem55236 {A B C : Type'} (P : type443 A B C) : term30 A B C P.
Proof. exact (conj (@lem55235 A B C P) (@lem55232 A B C P)). Qed.
Lemma lem55237 {A B C : Type'} (P : type443 A B C) : (term30 A B C P) = ((term0 A B C P) = (term1 A B C P)).
Proof. exact (@lem32 (term0 A B C P) (term1 A B C P)). Qed.
Lemma lem55238 {A B C : Type'} (P : type443 A B C) : (term0 A B C P) = (term1 A B C P).
Proof. exact (EQ_MP (@lem55237 A B C P) (@lem55236 A B C P)). Qed.
Lemma lem55243 {A B C : Type'} : term31 A B C.
Proof. exact (fun P : type443 A B C => @lem55238 A B C P). Qed.
