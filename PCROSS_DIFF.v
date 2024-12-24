Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_DIFF_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXTENSION_spec.
Require Import IN_DIFF_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8038230 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8038231 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8038232 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8038231 _141927 _141928 _141929 s) (@lem8038230 _141927 _141928 _141929 s)). Qed.
Lemma lem8038233 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8038232 _141927 _141928 _141929 s t). Qed.
Lemma lem8038234 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8038235 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8038234 _141927 _141928 _141929 s t) (@lem8038233 _141927 _141928 _141929 s t)). Qed.
Lemma lem8038236 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8038235 _141927 _141928 _141929 s t x). Qed.
Lemma lem8038237 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8038238 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8038237 _141927 _141928 _141929 x s t) (@lem8038236 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8038239 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8038238 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8038240 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038242 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem8038243 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem8038244 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem8038243 A s) (@lem8038242 A s)). Qed.
Lemma lem8038245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem8038244 A s t). Qed.
Lemma lem8038246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term12 A s t).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem8038247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (EQ_MP (@lem8038246 A s t) (@lem8038245 A s t)). Qed.
Lemma lem8038248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term13 A s t x.
Proof. exact (@lem8038247 A s t x). Qed.
Lemma lem8038249 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s t x) = ((term14 A x s t) = (term15 A s x t)).
Proof. exact (eq_refl (term13 A s t x)). Qed.
Lemma lem8038251 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8038252 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem8038253 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem8038252 A s) (@lem8038251 A s)). Qed.
Lemma lem8038254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem8038253 A s t). Qed.
Lemma lem8038255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem8038280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8038255 A s t) (@lem8038254 A s t)). Qed.
Lemma lem8038281 {_142619 _142620 _142621 : Type'} (s : type16 _142619 _142620 _142621) (t : type16 _142619 _142620 _142621) : (s = t) = (term20 _142619 _142620 _142621 s t).
Proof. exact (@lem8038280 (type2 _142619 _142620 _142621) s t). Qed.
Lemma lem8038282 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : ((term21 _142619 _142620 _142621 s t u) = (term22 _142619 _142620 _142621 t s u)) = (term23 _142619 _142620 _142621 t s u).
Proof. exact (@lem8038281 _142619 _142620 _142621 (term21 _142619 _142620 _142621 s t u) (term22 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038288 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8038289 {_142619 _142620 _142621 : Type'} (P : type16 _142619 _142620 _142621) : (term24 _142619 _142620 _142621 P) = (term25 _142619 _142620 _142621 P).
Proof. exact (@lem8038288 _142619 _142620 _142621 P). Qed.
Lemma lem8038290 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term26 _142619 _142620 _142621 t s u) = (term27 _142619 _142620 _142621 t s u).
Proof. exact (@lem8038289 _142619 _142620 _142621 (term28 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038291 {_142619 _142620 _142621 : Type'} (x : type2 _142619 _142620 _142621) (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term29 _142619 _142620 _142621 t s u x) = ((term30 _142619 _142620 _142621 x s t u) = (term31 _142619 _142620 _142621 x t s u)).
Proof. exact (eq_refl (term29 _142619 _142620 _142621 t s u x)). Qed.
Lemma lem8038292 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term32 _142619 _142620 _142621 t s u) = (term28 _142619 _142620 _142621 t s u).
Proof. exact (fun_ext (fun x : type2 _142619 _142620 _142621 => @lem8038291 _142619 _142620 _142621 x t s u)). Qed.
Lemma lem8038293 {_142619 _142620 _142621 : Type'} : (@all (cart _142619 (finite_sum _142620 _142621))) = (@all (cart _142619 (finite_sum _142620 _142621))).
Proof. exact (eq_refl (@all (cart _142619 (finite_sum _142620 _142621)))). Qed.
Lemma lem8038294 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term26 _142619 _142620 _142621 t s u) = (term23 _142619 _142620 _142621 t s u).
Proof. exact (MK_COMB (@lem8038293 _142619 _142620 _142621) (@lem8038292 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038296 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term33 _142619 _142620 _142621 t s u) = (term34 _142619 _142620 _142621 t s u).
Proof. exact (MK_COMB (@lem8038295) (@lem8038294 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038297 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term35 _142619 _142620 _142621 t s u x y) = ((term36 _142619 _142620 _142621 x y s t u) = (term37 _142619 _142620 _142621 x y t s u)).
Proof. exact (eq_refl (term35 _142619 _142620 _142621 t s u x y)). Qed.
Lemma lem8038298 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term38 _142619 _142620 _142621 t s u x) = (term39 _142619 _142620 _142621 x t s u).
Proof. exact (fun_ext (fun y : cart _142619 _142621 => @lem8038297 _142619 _142620 _142621 x y t s u)). Qed.
Lemma lem8038299 {_142619 _142621 : Type'} : (@all (cart _142619 _142621)) = (@all (cart _142619 _142621)).
Proof. exact (eq_refl (@all (cart _142619 _142621))). Qed.
Lemma lem8038300 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term40 _142619 _142620 _142621 t s u x) = (term41 _142619 _142620 _142621 x t s u).
Proof. exact (MK_COMB (@lem8038299 _142619 _142621) (@lem8038298 _142619 _142620 _142621 x t s u)). Qed.
Lemma lem8038301 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term42 _142619 _142620 _142621 t s u) = (term43 _142619 _142620 _142621 t s u).
Proof. exact (fun_ext (fun x : cart _142619 _142620 => @lem8038300 _142619 _142620 _142621 x t s u)). Qed.
Lemma lem8038302 {_142619 _142620 : Type'} : (@all (cart _142619 _142620)) = (@all (cart _142619 _142620)).
Proof. exact (eq_refl (@all (cart _142619 _142620))). Qed.
Lemma lem8038303 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term27 _142619 _142620 _142621 t s u) = (term44 _142619 _142620 _142621 t s u).
Proof. exact (MK_COMB (@lem8038302 _142619 _142620) (@lem8038301 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038304 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : ((term26 _142619 _142620 _142621 t s u) = (term27 _142619 _142620 _142621 t s u)) = ((term23 _142619 _142620 _142621 t s u) = (term44 _142619 _142620 _142621 t s u)).
Proof. exact (MK_COMB (@lem8038296 _142619 _142620 _142621 t s u) (@lem8038303 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038305 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term23 _142619 _142620 _142621 t s u) = (term44 _142619 _142620 _142621 t s u).
Proof. exact (EQ_MP (@lem8038304 _142619 _142620 _142621 t s u) (@lem8038290 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038312 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : ((term21 _142619 _142620 _142621 s t u) = (term22 _142619 _142620 _142621 t s u)) = (term44 _142619 _142620 _142621 t s u).
Proof. exact (TRANS (@lem8038282 _142619 _142620 _142621 t s u) (@lem8038305 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038324 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038325 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term7 _142619 _142620 _142621 x y s t) = (term8 _142619 _142620 _142621 x s y t).
Proof. exact (@lem8038324 _142619 _142620 _142621 x s y t). Qed.
Lemma lem8038326 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) (u : type24 _142619 _142621) : (term36 _142619 _142620 _142621 x y s t u) = (term45 _142619 _142620 _142621 x s y t u).
Proof. exact (@lem8038325 _142619 _142620 _142621 x s y (@DIFF (cart _142619 _142621) t u)). Qed.
Lemma lem8038330 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8038249 A s x t) (@lem8038248 A s t x)). Qed.
Lemma lem8038331 {_142619 _142621 : Type'} (s : type24 _142619 _142621) (x : cart _142619 _142621) (t : type24 _142619 _142621) : (term46 _142619 _142621 x s t) = (term47 _142619 _142621 s x t).
Proof. exact (@lem8038330 (cart _142619 _142621) s x t). Qed.
Lemma lem8038332 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term46 _142619 _142621 y t u) = (term47 _142619 _142621 t y u).
Proof. exact (@lem8038331 _142619 _142621 t y u). Qed.
Lemma lem8038335 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) : (term48 _142619 _142620 x s) = (term48 _142619 _142620 x s).
Proof. exact (eq_refl (term48 _142619 _142620 x s)). Qed.
Lemma lem8038336 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term45 _142619 _142620 _142621 x s y t u) = (term49 _142619 _142620 _142621 x s t y u).
Proof. exact (MK_COMB (@lem8038335 _142619 _142620 x s) (@lem8038332 _142619 _142621 t y u)). Qed.
Lemma lem8038339 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term36 _142619 _142620 _142621 x y s t u) = (term49 _142619 _142620 _142621 x s t y u).
Proof. exact (TRANS (@lem8038326 _142619 _142620 _142621 x s y t u) (@lem8038336 _142619 _142620 _142621 x s t y u)). Qed.
Lemma lem8038340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038341 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term50 _142619 _142620 _142621 x y s t u) = (term51 _142619 _142620 _142621 x s t y u).
Proof. exact (MK_COMB (@lem8038340) (@lem8038339 _142619 _142620 _142621 x s t y u)). Qed.
Lemma lem8038343 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8038249 A s x t) (@lem8038248 A s t x)). Qed.
Lemma lem8038344 {_142619 _142620 _142621 : Type'} (s : type16 _142619 _142620 _142621) (x : type2 _142619 _142620 _142621) (t : type16 _142619 _142620 _142621) : (term52 _142619 _142620 _142621 x s t) = (term53 _142619 _142620 _142621 s x t).
Proof. exact (@lem8038343 (type2 _142619 _142620 _142621) s x t). Qed.
Lemma lem8038345 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (y : cart _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term37 _142619 _142620 _142621 x y t s u) = (term54 _142619 _142620 _142621 t x y s u).
Proof. exact (@lem8038344 _142619 _142620 _142621 (@PCROSS _142619 _142620 _142621 s t) (@pastecart _142619 _142620 _142621 x y) (@PCROSS _142619 _142620 _142621 s u)). Qed.
Lemma lem8038349 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038350 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term7 _142619 _142620 _142621 x y s t) = (term8 _142619 _142620 _142621 x s y t).
Proof. exact (@lem8038349 _142619 _142620 _142621 x s y t). Qed.
Lemma lem8038353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038354 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term55 _142619 _142620 _142621 x y s t) = (term56 _142619 _142620 _142621 x s y t).
Proof. exact (MK_COMB (@lem8038353) (@lem8038350 _142619 _142620 _142621 x s y t)). Qed.
Lemma lem8038356 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038357 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term7 _142619 _142620 _142621 x y s t) = (term8 _142619 _142620 _142621 x s y t).
Proof. exact (@lem8038356 _142619 _142620 _142621 x s y t). Qed.
Lemma lem8038358 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term7 _142619 _142620 _142621 x y s u) = (term8 _142619 _142620 _142621 x s y u).
Proof. exact (@lem8038357 _142619 _142620 _142621 x s y u). Qed.
Lemma lem8038361 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038362 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term57 _142619 _142620 _142621 x y s u) = (term58 _142619 _142620 _142621 x s y u).
Proof. exact (MK_COMB (@lem8038361) (@lem8038358 _142619 _142620 _142621 x s y u)). Qed.
Lemma lem8038363 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term54 _142619 _142620 _142621 t x y s u) = (term59 _142619 _142620 _142621 t x s y u).
Proof. exact (MK_COMB (@lem8038354 _142619 _142620 _142621 x s y t) (@lem8038362 _142619 _142620 _142621 x s y u)). Qed.
Lemma lem8038366 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term37 _142619 _142620 _142621 x y t s u) = (term59 _142619 _142620 _142621 t x s y u).
Proof. exact (TRANS (@lem8038345 _142619 _142620 _142621 t x y s u) (@lem8038363 _142619 _142620 _142621 t x s y u)). Qed.
Lemma lem8038367 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term36 _142619 _142620 _142621 x y s t u) = (term37 _142619 _142620 _142621 x y t s u)) = ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)).
Proof. exact (MK_COMB (@lem8038341 _142619 _142620 _142621 x s t y u) (@lem8038366 _142619 _142620 _142621 t x s y u)). Qed.
Lemma lem8038372 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term39 _142619 _142620 _142621 x t s u) = (term60 _142619 _142620 _142621 t x s u).
Proof. exact (fun_ext (fun y : cart _142619 _142621 => @lem8038367 _142619 _142620 _142621 t x s y u)). Qed.
Lemma lem8038373 {_142619 _142621 : Type'} : (@all (cart _142619 _142621)) = (@all (cart _142619 _142621)).
Proof. exact (eq_refl (@all (cart _142619 _142621))). Qed.
Lemma lem8038374 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term41 _142619 _142620 _142621 x t s u) = (term61 _142619 _142620 _142621 t x s u).
Proof. exact (MK_COMB (@lem8038373 _142619 _142621) (@lem8038372 _142619 _142620 _142621 t x s u)). Qed.
Lemma lem8038381 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term43 _142619 _142620 _142621 t s u) = (term62 _142619 _142620 _142621 t s u).
Proof. exact (fun_ext (fun x : cart _142619 _142620 => @lem8038374 _142619 _142620 _142621 t x s u)). Qed.
Lemma lem8038382 {_142619 _142620 : Type'} : (@all (cart _142619 _142620)) = (@all (cart _142619 _142620)).
Proof. exact (eq_refl (@all (cart _142619 _142620))). Qed.
Lemma lem8038383 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : (term44 _142619 _142620 _142621 t s u) = (term63 _142619 _142620 _142621 t s u).
Proof. exact (MK_COMB (@lem8038382 _142619 _142620) (@lem8038381 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038390 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : ((term21 _142619 _142620 _142621 s t u) = (term22 _142619 _142620 _142621 t s u)) = (term63 _142619 _142620 _142621 t s u).
Proof. exact (TRANS (@lem8038312 _142619 _142620 _142621 t s u) (@lem8038383 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038391 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) : (term64 _142619 _142620 _142621 t s) = (term65 _142619 _142620 _142621 t s).
Proof. exact (fun_ext (fun u : type24 _142619 _142621 => @lem8038390 _142619 _142620 _142621 t s u)). Qed.
Lemma lem8038392 {_142619 _142621 : Type'} : (@all ((cart _142619 _142621) -> Prop)) = (@all ((cart _142619 _142621) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142619 _142621) -> Prop))). Qed.
Lemma lem8038393 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) : (term66 _142619 _142620 _142621 t s) = (term67 _142619 _142620 _142621 t s).
Proof. exact (MK_COMB (@lem8038392 _142619 _142621) (@lem8038391 _142619 _142620 _142621 t s)). Qed.
Lemma lem8038400 {_142619 _142620 _142621 : Type'} (s : type24 _142619 _142620) : (term68 _142619 _142620 _142621 s) = (term69 _142619 _142620 _142621 s).
Proof. exact (fun_ext (fun t : type24 _142619 _142621 => @lem8038393 _142619 _142620 _142621 t s)). Qed.
Lemma lem8038401 {_142619 _142621 : Type'} : (@all ((cart _142619 _142621) -> Prop)) = (@all ((cart _142619 _142621) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142619 _142621) -> Prop))). Qed.
Lemma lem8038402 {_142619 _142620 _142621 : Type'} (s : type24 _142619 _142620) : (term70 _142619 _142620 _142621 s) = (term71 _142619 _142620 _142621 s).
Proof. exact (MK_COMB (@lem8038401 _142619 _142621) (@lem8038400 _142619 _142620 _142621 s)). Qed.
Lemma lem8038409 {_142619 _142620 _142621 : Type'} : (term72 _142619 _142620 _142621) = (term73 _142619 _142620 _142621).
Proof. exact (fun_ext (fun s : type24 _142619 _142620 => @lem8038402 _142619 _142620 _142621 s)). Qed.
Lemma lem8038410 {_142619 _142620 : Type'} : (@all ((cart _142619 _142620) -> Prop)) = (@all ((cart _142619 _142620) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142619 _142620) -> Prop))). Qed.
Lemma lem8038411 {_142619 _142620 _142621 : Type'} : (term74 _142619 _142620 _142621) = (term75 _142619 _142620 _142621).
Proof. exact (MK_COMB (@lem8038410 _142619 _142620) (@lem8038409 _142619 _142620 _142621)). Qed.
Lemma lem8038418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038419 {_142619 _142620 _142621 : Type'} : (term76 _142619 _142620 _142621) = (term77 _142619 _142620 _142621).
Proof. exact (MK_COMB (@lem8038418) (@lem8038411 _142619 _142620 _142621)). Qed.
Lemma lem8038441 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem8038255 A s t) (@lem8038254 A s t)). Qed.
Lemma lem8038442 {_142655 _142656 _142657 : Type'} (s : type16 _142655 _142656 _142657) (t : type16 _142655 _142656 _142657) : (s = t) = (term20 _142655 _142656 _142657 s t).
Proof. exact (@lem8038441 (type2 _142655 _142656 _142657) s t). Qed.
Lemma lem8038443 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : ((term78 _142655 _142656 _142657 s t u) = (term79 _142655 _142656 _142657 s t u)) = (term80 _142655 _142656 _142657 s t u).
Proof. exact (@lem8038442 _142655 _142656 _142657 (term78 _142655 _142656 _142657 s t u) (term79 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038449 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term24 _140454 _140455 _140456 P) = (term25 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8038450 {_142655 _142656 _142657 : Type'} (P : type16 _142655 _142656 _142657) : (term24 _142655 _142656 _142657 P) = (term25 _142655 _142656 _142657 P).
Proof. exact (@lem8038449 _142655 _142656 _142657 P). Qed.
Lemma lem8038451 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term81 _142655 _142656 _142657 s t u) = (term82 _142655 _142656 _142657 s t u).
Proof. exact (@lem8038450 _142655 _142656 _142657 (term83 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038452 {_142655 _142656 _142657 : Type'} (x : type2 _142655 _142656 _142657) (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term84 _142655 _142656 _142657 s t u x) = ((term85 _142655 _142656 _142657 x s t u) = (term86 _142655 _142656 _142657 x s t u)).
Proof. exact (eq_refl (term84 _142655 _142656 _142657 s t u x)). Qed.
Lemma lem8038453 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term87 _142655 _142656 _142657 s t u) = (term83 _142655 _142656 _142657 s t u).
Proof. exact (fun_ext (fun x : type2 _142655 _142656 _142657 => @lem8038452 _142655 _142656 _142657 x s t u)). Qed.
Lemma lem8038454 {_142655 _142656 _142657 : Type'} : (@all (cart _142655 (finite_sum _142656 _142657))) = (@all (cart _142655 (finite_sum _142656 _142657))).
Proof. exact (eq_refl (@all (cart _142655 (finite_sum _142656 _142657)))). Qed.
Lemma lem8038455 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term81 _142655 _142656 _142657 s t u) = (term80 _142655 _142656 _142657 s t u).
Proof. exact (MK_COMB (@lem8038454 _142655 _142656 _142657) (@lem8038453 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038457 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term88 _142655 _142656 _142657 s t u) = (term89 _142655 _142656 _142657 s t u).
Proof. exact (MK_COMB (@lem8038456) (@lem8038455 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038458 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (y : cart _142655 _142657) (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term90 _142655 _142656 _142657 s t u x y) = ((term91 _142655 _142656 _142657 x y s t u) = (term92 _142655 _142656 _142657 x y s t u)).
Proof. exact (eq_refl (term90 _142655 _142656 _142657 s t u x y)). Qed.
Lemma lem8038459 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term93 _142655 _142656 _142657 s t u x) = (term94 _142655 _142656 _142657 x s t u).
Proof. exact (fun_ext (fun y : cart _142655 _142657 => @lem8038458 _142655 _142656 _142657 x y s t u)). Qed.
Lemma lem8038460 {_142655 _142657 : Type'} : (@all (cart _142655 _142657)) = (@all (cart _142655 _142657)).
Proof. exact (eq_refl (@all (cart _142655 _142657))). Qed.
Lemma lem8038461 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term95 _142655 _142656 _142657 s t u x) = (term96 _142655 _142656 _142657 x s t u).
Proof. exact (MK_COMB (@lem8038460 _142655 _142657) (@lem8038459 _142655 _142656 _142657 x s t u)). Qed.
Lemma lem8038462 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term97 _142655 _142656 _142657 s t u) = (term98 _142655 _142656 _142657 s t u).
Proof. exact (fun_ext (fun x : cart _142655 _142656 => @lem8038461 _142655 _142656 _142657 x s t u)). Qed.
Lemma lem8038463 {_142655 _142656 : Type'} : (@all (cart _142655 _142656)) = (@all (cart _142655 _142656)).
Proof. exact (eq_refl (@all (cart _142655 _142656))). Qed.
Lemma lem8038464 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term82 _142655 _142656 _142657 s t u) = (term99 _142655 _142656 _142657 s t u).
Proof. exact (MK_COMB (@lem8038463 _142655 _142656) (@lem8038462 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038465 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : ((term81 _142655 _142656 _142657 s t u) = (term82 _142655 _142656 _142657 s t u)) = ((term80 _142655 _142656 _142657 s t u) = (term99 _142655 _142656 _142657 s t u)).
Proof. exact (MK_COMB (@lem8038457 _142655 _142656 _142657 s t u) (@lem8038464 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038466 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term80 _142655 _142656 _142657 s t u) = (term99 _142655 _142656 _142657 s t u).
Proof. exact (EQ_MP (@lem8038465 _142655 _142656 _142657 s t u) (@lem8038451 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038473 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : ((term78 _142655 _142656 _142657 s t u) = (term79 _142655 _142656 _142657 s t u)) = (term99 _142655 _142656 _142657 s t u).
Proof. exact (TRANS (@lem8038443 _142655 _142656 _142657 s t u) (@lem8038466 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038485 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038486 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (y : cart _142655 _142657) (t : type24 _142655 _142657) : (term7 _142655 _142656 _142657 x y s t) = (term8 _142655 _142656 _142657 x s y t).
Proof. exact (@lem8038485 _142655 _142656 _142657 x s y t). Qed.
Lemma lem8038487 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term91 _142655 _142656 _142657 x y s t u) = (term100 _142655 _142656 _142657 x s t y u).
Proof. exact (@lem8038486 _142655 _142656 _142657 x (@DIFF (cart _142655 _142656) s t) y u). Qed.
Lemma lem8038491 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8038249 A s x t) (@lem8038248 A s t x)). Qed.
Lemma lem8038492 {_142655 _142656 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term46 _142655 _142656 x s t) = (term47 _142655 _142656 s x t).
Proof. exact (@lem8038491 (cart _142655 _142656) s x t). Qed.
Lemma lem8038495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038496 {_142655 _142656 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term101 _142655 _142656 x s t) = (term102 _142655 _142656 s x t).
Proof. exact (MK_COMB (@lem8038495) (@lem8038492 _142655 _142656 s x t)). Qed.
Lemma lem8038497 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (eq_refl (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038498 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term100 _142655 _142656 _142657 x s t y u) = (term103 _142655 _142656 _142657 s x t y u).
Proof. exact (MK_COMB (@lem8038496 _142655 _142656 s x t) (@lem8038497 _142655 _142657 y u)). Qed.
Lemma lem8038501 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term91 _142655 _142656 _142657 x y s t u) = (term103 _142655 _142656 _142657 s x t y u).
Proof. exact (TRANS (@lem8038487 _142655 _142656 _142657 x s t y u) (@lem8038498 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038503 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term104 _142655 _142656 _142657 x y s t u) = (term105 _142655 _142656 _142657 s x t y u).
Proof. exact (MK_COMB (@lem8038502) (@lem8038501 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038505 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A x s t) = (term15 A s x t).
Proof. exact (EQ_MP (@lem8038249 A s x t) (@lem8038248 A s t x)). Qed.
Lemma lem8038506 {_142655 _142656 _142657 : Type'} (s : type16 _142655 _142656 _142657) (x : type2 _142655 _142656 _142657) (t : type16 _142655 _142656 _142657) : (term52 _142655 _142656 _142657 x s t) = (term53 _142655 _142656 _142657 s x t).
Proof. exact (@lem8038505 (type2 _142655 _142656 _142657) s x t). Qed.
Lemma lem8038507 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (y : cart _142655 _142657) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term92 _142655 _142656 _142657 x y s t u) = (term106 _142655 _142656 _142657 s x y t u).
Proof. exact (@lem8038506 _142655 _142656 _142657 (@PCROSS _142655 _142656 _142657 s u) (@pastecart _142655 _142656 _142657 x y) (@PCROSS _142655 _142656 _142657 t u)). Qed.
Lemma lem8038511 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038512 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (y : cart _142655 _142657) (t : type24 _142655 _142657) : (term7 _142655 _142656 _142657 x y s t) = (term8 _142655 _142656 _142657 x s y t).
Proof. exact (@lem8038511 _142655 _142656 _142657 x s y t). Qed.
Lemma lem8038513 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term7 _142655 _142656 _142657 x y s u) = (term8 _142655 _142656 _142657 x s y u).
Proof. exact (@lem8038512 _142655 _142656 _142657 x s y u). Qed.
Lemma lem8038516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038517 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term55 _142655 _142656 _142657 x y s u) = (term56 _142655 _142656 _142657 x s y u).
Proof. exact (MK_COMB (@lem8038516) (@lem8038513 _142655 _142656 _142657 x s y u)). Qed.
Lemma lem8038519 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8038240 _141927 _141928 _141929 x s y t) (@lem8038239 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8038520 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (y : cart _142655 _142657) (t : type24 _142655 _142657) : (term7 _142655 _142656 _142657 x y s t) = (term8 _142655 _142656 _142657 x s y t).
Proof. exact (@lem8038519 _142655 _142656 _142657 x s y t). Qed.
Lemma lem8038521 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term7 _142655 _142656 _142657 x y t u) = (term8 _142655 _142656 _142657 x t y u).
Proof. exact (@lem8038520 _142655 _142656 _142657 x t y u). Qed.
Lemma lem8038524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038525 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term57 _142655 _142656 _142657 x y t u) = (term58 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038524) (@lem8038521 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038526 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term106 _142655 _142656 _142657 s x y t u) = (term107 _142655 _142656 _142657 s x t y u).
Proof. exact (MK_COMB (@lem8038517 _142655 _142656 _142657 x s y u) (@lem8038525 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038529 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term92 _142655 _142656 _142657 x y s t u) = (term107 _142655 _142656 _142657 s x t y u).
Proof. exact (TRANS (@lem8038507 _142655 _142656 _142657 s x y t u) (@lem8038526 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038530 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term91 _142655 _142656 _142657 x y s t u) = (term92 _142655 _142656 _142657 x y s t u)) = ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)).
Proof. exact (MK_COMB (@lem8038503 _142655 _142656 _142657 s x t y u) (@lem8038529 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038535 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term94 _142655 _142656 _142657 x s t u) = (term108 _142655 _142656 _142657 s x t u).
Proof. exact (fun_ext (fun y : cart _142655 _142657 => @lem8038530 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038536 {_142655 _142657 : Type'} : (@all (cart _142655 _142657)) = (@all (cart _142655 _142657)).
Proof. exact (eq_refl (@all (cart _142655 _142657))). Qed.
Lemma lem8038537 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term96 _142655 _142656 _142657 x s t u) = (term109 _142655 _142656 _142657 s x t u).
Proof. exact (MK_COMB (@lem8038536 _142655 _142657) (@lem8038535 _142655 _142656 _142657 s x t u)). Qed.
Lemma lem8038544 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term98 _142655 _142656 _142657 s t u) = (term110 _142655 _142656 _142657 s t u).
Proof. exact (fun_ext (fun x : cart _142655 _142656 => @lem8038537 _142655 _142656 _142657 s x t u)). Qed.
Lemma lem8038545 {_142655 _142656 : Type'} : (@all (cart _142655 _142656)) = (@all (cart _142655 _142656)).
Proof. exact (eq_refl (@all (cart _142655 _142656))). Qed.
Lemma lem8038546 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : (term99 _142655 _142656 _142657 s t u) = (term111 _142655 _142656 _142657 s t u).
Proof. exact (MK_COMB (@lem8038545 _142655 _142656) (@lem8038544 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038553 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : ((term78 _142655 _142656 _142657 s t u) = (term79 _142655 _142656 _142657 s t u)) = (term111 _142655 _142656 _142657 s t u).
Proof. exact (TRANS (@lem8038473 _142655 _142656 _142657 s t u) (@lem8038546 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038554 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) : (term112 _142655 _142656 _142657 s t) = (term113 _142655 _142656 _142657 s t).
Proof. exact (fun_ext (fun u : type24 _142655 _142657 => @lem8038553 _142655 _142656 _142657 s t u)). Qed.
Lemma lem8038555 {_142655 _142657 : Type'} : (@all ((cart _142655 _142657) -> Prop)) = (@all ((cart _142655 _142657) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142655 _142657) -> Prop))). Qed.
Lemma lem8038556 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) : (term114 _142655 _142656 _142657 s t) = (term115 _142655 _142656 _142657 s t).
Proof. exact (MK_COMB (@lem8038555 _142655 _142657) (@lem8038554 _142655 _142656 _142657 s t)). Qed.
Lemma lem8038563 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) : (term116 _142655 _142656 _142657 s) = (term117 _142655 _142656 _142657 s).
Proof. exact (fun_ext (fun t : type24 _142655 _142656 => @lem8038556 _142655 _142656 _142657 s t)). Qed.
Lemma lem8038564 {_142655 _142656 : Type'} : (@all ((cart _142655 _142656) -> Prop)) = (@all ((cart _142655 _142656) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142655 _142656) -> Prop))). Qed.
Lemma lem8038565 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) : (term118 _142655 _142656 _142657 s) = (term119 _142655 _142656 _142657 s).
Proof. exact (MK_COMB (@lem8038564 _142655 _142656) (@lem8038563 _142655 _142656 _142657 s)). Qed.
Lemma lem8038572 {_142655 _142656 _142657 : Type'} : (term120 _142655 _142656 _142657) = (term121 _142655 _142656 _142657).
Proof. exact (fun_ext (fun s : type24 _142655 _142656 => @lem8038565 _142655 _142656 _142657 s)). Qed.
Lemma lem8038573 {_142655 _142656 : Type'} : (@all ((cart _142655 _142656) -> Prop)) = (@all ((cart _142655 _142656) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142655 _142656) -> Prop))). Qed.
Lemma lem8038574 {_142655 _142656 _142657 : Type'} : (term122 _142655 _142656 _142657) = (term123 _142655 _142656 _142657).
Proof. exact (MK_COMB (@lem8038573 _142655 _142656) (@lem8038572 _142655 _142656 _142657)). Qed.
Lemma lem8038581 {_142619 _142620 _142621 _142655 _142656 _142657 : Type'} : (term124 _142619 _142620 _142621 _142655 _142656 _142657) = (term125 _142619 _142620 _142621 _142655 _142656 _142657).
Proof. exact (MK_COMB (@lem8038419 _142619 _142620 _142621) (@lem8038574 _142655 _142656 _142657)). Qed.
Lemma lem8038584 {_142619 _142620 _142621 _142655 _142656 _142657 : Type'} : (term125 _142619 _142620 _142621 _142655 _142656 _142657) = (term124 _142619 _142620 _142621 _142655 _142656 _142657).
Proof. exact (SYM (@lem8038581 _142619 _142620 _142621 _142655 _142656 _142657)). Qed.
Lemma lem8038599 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) : term126 _142619 _142620 x s.
Proof. exact (@lem9851 (@IN (cart _142619 _142620) x s)). Qed.
Lemma lem8038600 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) : (term126 _142619 _142620 x s) = (term127 _142619 _142620 x s).
Proof. exact (eq_refl (term126 _142619 _142620 x s)). Qed.
Lemma lem8038601 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) : term127 _142619 _142620 x s.
Proof. exact (EQ_MP (@lem8038600 _142619 _142620 x s) (@lem8038599 _142619 _142620 x s)). Qed.
Lemma lem8038602 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = True) : (@IN (cart _142619 _142620) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8038603 {_142619 _142620 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = False) : (@IN (cart _142619 _142620) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8038618 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term128 _142619 _142621 t y u) = (term128 _142619 _142621 t y u).
Proof. exact (eq_refl (term128 _142619 _142621 t y u)). Qed.
Lemma lem8038619 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = True) : (term129 _142619 _142620 _142621 t y u x s) = (term130 _142619 _142621 t y u).
Proof. exact (MK_COMB (@lem8038618 _142619 _142621 t y u) (@lem8038602 _142619 _142620 x s h1)). Qed.
Lemma lem8038620 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term130 _142619 _142621 t y u) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)).
Proof. exact (eq_refl (term130 _142619 _142621 t y u)). Qed.
Lemma lem8038621 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) : (term133 _142619 _142620 _142621 t y u x s) = (term133 _142619 _142620 _142621 t y u x s).
Proof. exact (eq_refl (term133 _142619 _142620 _142621 t y u x s)). Qed.
Lemma lem8038622 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = (term130 _142619 _142621 t y u)) = ((term129 _142619 _142620 _142621 t y u x s) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u))).
Proof. exact (MK_COMB (@lem8038621 _142619 _142620 _142621 t y u x s) (@lem8038620 _142619 _142621 t y u)). Qed.
Lemma lem8038623 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term129 _142619 _142620 _142621 t y u x s) = ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)).
Proof. exact (eq_refl (term129 _142619 _142620 _142621 t y u x s)). Qed.
Lemma lem8038624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038625 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term133 _142619 _142620 _142621 t y u x s) = (term134 _142619 _142620 _142621 t x s y u).
Proof. exact (MK_COMB (@lem8038624) (@lem8038623 _142619 _142620 _142621 t x s y u)). Qed.
Lemma lem8038626 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)).
Proof. exact (eq_refl ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u))). Qed.
Lemma lem8038627 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u))) = (((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u))).
Proof. exact (MK_COMB (@lem8038625 _142619 _142620 _142621 t x s y u) (@lem8038626 _142619 _142621 t y u)). Qed.
Lemma lem8038628 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = (term130 _142619 _142621 t y u)) = (((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u))).
Proof. exact (TRANS (@lem8038622 _142619 _142620 _142621 x s t y u) (@lem8038627 _142619 _142620 _142621 x s t y u)). Qed.
Lemma lem8038629 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = True) : ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)).
Proof. exact (EQ_MP (@lem8038628 _142619 _142620 _142621 x s t y u) (@lem8038619 _142619 _142620 _142621 t y u x s h1)). Qed.
Lemma lem8038630 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = True) : ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)) = ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)).
Proof. exact (SYM (@lem8038629 _142619 _142620 _142621 t y u x s h1)). Qed.
Lemma lem8038631 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term128 _142619 _142621 t y u) = (term128 _142619 _142621 t y u).
Proof. exact (eq_refl (term128 _142619 _142621 t y u)). Qed.
Lemma lem8038632 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = False) : (term129 _142619 _142620 _142621 t y u x s) = (term135 _142619 _142621 t y u).
Proof. exact (MK_COMB (@lem8038631 _142619 _142621 t y u) (@lem8038603 _142619 _142620 x s h1)). Qed.
Lemma lem8038633 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term135 _142619 _142621 t y u) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)).
Proof. exact (eq_refl (term135 _142619 _142621 t y u)). Qed.
Lemma lem8038634 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) : (term133 _142619 _142620 _142621 t y u x s) = (term133 _142619 _142620 _142621 t y u x s).
Proof. exact (eq_refl (term133 _142619 _142620 _142621 t y u x s)). Qed.
Lemma lem8038635 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = (term135 _142619 _142621 t y u)) = ((term129 _142619 _142620 _142621 t y u x s) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u))).
Proof. exact (MK_COMB (@lem8038634 _142619 _142620 _142621 t y u x s) (@lem8038633 _142619 _142621 t y u)). Qed.
Lemma lem8038636 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term129 _142619 _142620 _142621 t y u x s) = ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)).
Proof. exact (eq_refl (term129 _142619 _142620 _142621 t y u x s)). Qed.
Lemma lem8038637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038638 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term133 _142619 _142620 _142621 t y u x s) = (term134 _142619 _142620 _142621 t x s y u).
Proof. exact (MK_COMB (@lem8038637) (@lem8038636 _142619 _142620 _142621 t x s y u)). Qed.
Lemma lem8038639 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)).
Proof. exact (eq_refl ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u))). Qed.
Lemma lem8038640 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u))) = (((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u))).
Proof. exact (MK_COMB (@lem8038638 _142619 _142620 _142621 t x s y u) (@lem8038639 _142619 _142621 t y u)). Qed.
Lemma lem8038641 {_142619 _142620 _142621 : Type'} (x : cart _142619 _142620) (s : type24 _142619 _142620) (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term129 _142619 _142620 _142621 t y u x s) = (term135 _142619 _142621 t y u)) = (((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u))).
Proof. exact (TRANS (@lem8038635 _142619 _142620 _142621 x s t y u) (@lem8038640 _142619 _142620 _142621 x s t y u)). Qed.
Lemma lem8038642 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = False) : ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)) = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)).
Proof. exact (EQ_MP (@lem8038641 _142619 _142620 _142621 x s t y u) (@lem8038632 _142619 _142620 _142621 t y u x s h1)). Qed.
Lemma lem8038643 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = False) : ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)) = ((term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u)).
Proof. exact (SYM (@lem8038642 _142619 _142620 _142621 t y u x s h1)). Qed.
Lemma lem8038647 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038648 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term131 _142619 _142621 t y u) = (term47 _142619 _142621 t y u).
Proof. exact (@lem8038647 (term47 _142619 _142621 t y u)). Qed.
Lemma lem8038651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038652 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term138 _142619 _142621 t y u) = (term139 _142619 _142621 t y u).
Proof. exact (MK_COMB (@lem8038651) (@lem8038648 _142619 _142621 t y u)). Qed.
Lemma lem8038656 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038657 {_142619 _142621 : Type'} (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term140 _142619 _142621 y t) = (@IN (cart _142619 _142621) y t).
Proof. exact (@lem8038656 (@IN (cart _142619 _142621) y t)). Qed.
Lemma lem8038658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038659 {_142619 _142621 : Type'} (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term141 _142619 _142621 y t) = (term48 _142619 _142621 y t).
Proof. exact (MK_COMB (@lem8038658) (@lem8038657 _142619 _142621 y t)). Qed.
Lemma lem8038661 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038662 {_142619 _142621 : Type'} (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term140 _142619 _142621 y u) = (@IN (cart _142619 _142621) y u).
Proof. exact (@lem8038661 (@IN (cart _142619 _142621) y u)). Qed.
Lemma lem8038663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038664 {_142619 _142621 : Type'} (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term142 _142619 _142621 y u) = (term143 _142619 _142621 y u).
Proof. exact (MK_COMB (@lem8038663) (@lem8038662 _142619 _142621 y u)). Qed.
Lemma lem8038665 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term132 _142619 _142621 t y u) = (term47 _142619 _142621 t y u).
Proof. exact (MK_COMB (@lem8038659 _142619 _142621 y t) (@lem8038664 _142619 _142621 y u)). Qed.
Lemma lem8038668 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)) = ((term47 _142619 _142621 t y u) = (term47 _142619 _142621 t y u)).
Proof. exact (MK_COMB (@lem8038652 _142619 _142621 t y u) (@lem8038665 _142619 _142621 t y u)). Qed.
Lemma lem8038670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8038671 (x : Prop) : (x = x) = True.
Proof. exact (@lem8038670 Prop x). Qed.
Lemma lem8038672 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term47 _142619 _142621 t y u) = (term47 _142619 _142621 t y u)) = True.
Proof. exact (@lem8038671 (term47 _142619 _142621 t y u)). Qed.
Lemma lem8038673 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)) = True.
Proof. exact (TRANS (@lem8038668 _142619 _142621 t y u) (@lem8038672 _142619 _142621 t y u)). Qed.
Lemma lem8038674 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : True = ((term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u)).
Proof. exact (SYM (@lem8038673 _142619 _142621 t y u)). Qed.
Lemma lem8038675 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term131 _142619 _142621 t y u) = (term132 _142619 _142621 t y u).
Proof. exact (EQ_MP (@lem8038674 _142619 _142621 t y u) (@lem0)). Qed.
Lemma lem8038679 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038680 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term136 _142619 _142621 t y u) = False.
Proof. exact (@lem8038679 (term47 _142619 _142621 t y u)). Qed.
Lemma lem8038681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038682 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term144 _142619 _142621 t y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8038681) (@lem8038680 _142619 _142621 t y u)). Qed.
Lemma lem8038686 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038687 {_142619 _142621 : Type'} (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term145 _142619 _142621 y t) = False.
Proof. exact (@lem8038686 (@IN (cart _142619 _142621) y t)). Qed.
Lemma lem8038688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038689 {_142619 _142621 : Type'} (y : cart _142619 _142621) (t : type24 _142619 _142621) : (term146 _142619 _142621 y t) = (and False).
Proof. exact (MK_COMB (@lem8038688) (@lem8038687 _142619 _142621 y t)). Qed.
Lemma lem8038691 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038692 {_142619 _142621 : Type'} (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term145 _142619 _142621 y u) = False.
Proof. exact (@lem8038691 (@IN (cart _142619 _142621) y u)). Qed.
Lemma lem8038693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038694 {_142619 _142621 : Type'} (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term147 _142619 _142621 y u) = (~ False).
Proof. exact (MK_COMB (@lem8038693) (@lem8038692 _142619 _142621 y u)). Qed.
Lemma lem8038696 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038697 {_142619 _142621 : Type'} (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term147 _142619 _142621 y u) = True.
Proof. exact (TRANS (@lem8038694 _142619 _142621 y u) (@lem8038696)). Qed.
Lemma lem8038698 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term137 _142619 _142621 t y u) = (False /\ True).
Proof. exact (MK_COMB (@lem8038689 _142619 _142621 y t) (@lem8038697 _142619 _142621 y u)). Qed.
Lemma lem8038700 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038701 : (False /\ True) = False.
Proof. exact (@lem8038700 True). Qed.
Lemma lem8038702 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term137 _142619 _142621 t y u) = False.
Proof. exact (TRANS (@lem8038698 _142619 _142621 t y u) (@lem8038701)). Qed.
Lemma lem8038703 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)) = (False = False).
Proof. exact (MK_COMB (@lem8038682 _142619 _142621 t y u) (@lem8038702 _142619 _142621 t y u)). Qed.
Lemma lem8038705 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8038706 : (False = False) = (~ False).
Proof. exact (@lem8038705 False). Qed.
Lemma lem8038708 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038709 : (False = False) = True.
Proof. exact (TRANS (@lem8038706) (@lem8038708)). Qed.
Lemma lem8038710 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)) = True.
Proof. exact (TRANS (@lem8038703 _142619 _142621 t y u) (@lem8038709)). Qed.
Lemma lem8038711 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : True = ((term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u)).
Proof. exact (SYM (@lem8038710 _142619 _142621 t y u)). Qed.
Lemma lem8038712 {_142619 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term136 _142619 _142621 t y u) = (term137 _142619 _142621 t y u).
Proof. exact (EQ_MP (@lem8038711 _142619 _142621 t y u) (@lem0)). Qed.
Lemma lem8038713 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = False) : (term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u).
Proof. exact (EQ_MP (@lem8038643 _142619 _142620 _142621 t y u x s h1) (@lem8038712 _142619 _142621 t y u)). Qed.
Lemma lem8038714 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (y : cart _142619 _142621) (u : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (h1 : (@IN (cart _142619 _142620) x s) = True) : (term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u).
Proof. exact (EQ_MP (@lem8038630 _142619 _142620 _142621 t y u x s h1) (@lem8038675 _142619 _142621 t y u)). Qed.
Lemma lem8038717 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (y : cart _142619 _142621) (u : type24 _142619 _142621) : (term49 _142619 _142620 _142621 x s t y u) = (term59 _142619 _142620 _142621 t x s y u).
Proof. exact (or_elim (@lem8038601 _142619 _142620 x s) (fun h0 : (@IN (cart _142619 _142620) x s) = True => @lem8038714 _142619 _142620 _142621 t y u x s h0) (fun h0 : (@IN (cart _142619 _142620) x s) = False => @lem8038713 _142619 _142620 _142621 t y u x s h0)). Qed.
Lemma lem8038732 {_142655 _142656 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) : term126 _142655 _142656 x s.
Proof. exact (@lem9851 (@IN (cart _142655 _142656) x s)). Qed.
Lemma lem8038733 {_142655 _142656 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) : (term126 _142655 _142656 x s) = (term127 _142655 _142656 x s).
Proof. exact (eq_refl (term126 _142655 _142656 x s)). Qed.
Lemma lem8038734 {_142655 _142656 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) : term127 _142655 _142656 x s.
Proof. exact (EQ_MP (@lem8038733 _142655 _142656 x s) (@lem8038732 _142655 _142656 x s)). Qed.
Lemma lem8038735 {_142655 _142656 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = True) : (@IN (cart _142655 _142656) x s) = True.
Proof. exact (h1). Qed.
Lemma lem8038736 {_142655 _142656 : Type'} (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = False) : (@IN (cart _142655 _142656) x s) = False.
Proof. exact (h1). Qed.
Lemma lem8038751 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term148 _142655 _142656 _142657 x t y u) = (term148 _142655 _142656 _142657 x t y u).
Proof. exact (eq_refl (term148 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038752 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = True) : (term149 _142655 _142656 _142657 t y u x s) = (term150 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038751 _142655 _142656 _142657 x t y u) (@lem8038735 _142655 _142656 x s h1)). Qed.
Lemma lem8038753 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term150 _142655 _142656 _142657 x t y u) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl (term150 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038754 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) : (term153 _142655 _142656 _142657 t y u x s) = (term153 _142655 _142656 _142657 t y u x s).
Proof. exact (eq_refl (term153 _142655 _142656 _142657 t y u x s)). Qed.
Lemma lem8038755 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = (term150 _142655 _142656 _142657 x t y u)) = ((term149 _142655 _142656 _142657 t y u x s) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u))).
Proof. exact (MK_COMB (@lem8038754 _142655 _142656 _142657 t y u x s) (@lem8038753 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038756 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term149 _142655 _142656 _142657 t y u x s) = ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)).
Proof. exact (eq_refl (term149 _142655 _142656 _142657 t y u x s)). Qed.
Lemma lem8038757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038758 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term153 _142655 _142656 _142657 t y u x s) = (term154 _142655 _142656 _142657 s x t y u).
Proof. exact (MK_COMB (@lem8038757) (@lem8038756 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038759 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u))). Qed.
Lemma lem8038760 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u))) = (((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u))).
Proof. exact (MK_COMB (@lem8038758 _142655 _142656 _142657 s x t y u) (@lem8038759 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038761 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = (term150 _142655 _142656 _142657 x t y u)) = (((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u))).
Proof. exact (TRANS (@lem8038755 _142655 _142656 _142657 s x t y u) (@lem8038760 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038762 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = True) : ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)).
Proof. exact (EQ_MP (@lem8038761 _142655 _142656 _142657 s x t y u) (@lem8038752 _142655 _142656 _142657 t y u x s h1)). Qed.
Lemma lem8038763 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = True) : ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)) = ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)).
Proof. exact (SYM (@lem8038762 _142655 _142656 _142657 t y u x s h1)). Qed.
Lemma lem8038764 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term148 _142655 _142656 _142657 x t y u) = (term148 _142655 _142656 _142657 x t y u).
Proof. exact (eq_refl (term148 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038765 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = False) : (term149 _142655 _142656 _142657 t y u x s) = (term155 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038764 _142655 _142656 _142657 x t y u) (@lem8038736 _142655 _142656 x s h1)). Qed.
Lemma lem8038766 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term155 _142655 _142656 _142657 x t y u) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl (term155 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038767 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) : (term153 _142655 _142656 _142657 t y u x s) = (term153 _142655 _142656 _142657 t y u x s).
Proof. exact (eq_refl (term153 _142655 _142656 _142657 t y u x s)). Qed.
Lemma lem8038768 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = (term155 _142655 _142656 _142657 x t y u)) = ((term149 _142655 _142656 _142657 t y u x s) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u))).
Proof. exact (MK_COMB (@lem8038767 _142655 _142656 _142657 t y u x s) (@lem8038766 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038769 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term149 _142655 _142656 _142657 t y u x s) = ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)).
Proof. exact (eq_refl (term149 _142655 _142656 _142657 t y u x s)). Qed.
Lemma lem8038770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038771 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term153 _142655 _142656 _142657 t y u x s) = (term154 _142655 _142656 _142657 s x t y u).
Proof. exact (MK_COMB (@lem8038770) (@lem8038769 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038772 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u))). Qed.
Lemma lem8038773 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u))) = (((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u))).
Proof. exact (MK_COMB (@lem8038771 _142655 _142656 _142657 s x t y u) (@lem8038772 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038774 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term149 _142655 _142656 _142657 t y u x s) = (term155 _142655 _142656 _142657 x t y u)) = (((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u))).
Proof. exact (TRANS (@lem8038768 _142655 _142656 _142657 s x t y u) (@lem8038773 _142655 _142656 _142657 s x t y u)). Qed.
Lemma lem8038775 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = False) : ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)) = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)).
Proof. exact (EQ_MP (@lem8038774 _142655 _142656 _142657 s x t y u) (@lem8038765 _142655 _142656 _142657 t y u x s h1)). Qed.
Lemma lem8038776 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = False) : ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)) = ((term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u)).
Proof. exact (SYM (@lem8038775 _142655 _142656 _142657 t y u x s h1)). Qed.
Lemma lem8038782 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038783 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term158 _142655 _142656 x t) = (term143 _142655 _142656 x t).
Proof. exact (@lem8038782 (term143 _142655 _142656 x t)). Qed.
Lemma lem8038784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038785 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term159 _142655 _142656 x t) = (term160 _142655 _142656 x t).
Proof. exact (MK_COMB (@lem8038784) (@lem8038783 _142655 _142656 x t)). Qed.
Lemma lem8038786 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (eq_refl (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038787 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term151 _142655 _142656 _142657 x t y u) = (term161 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038785 _142655 _142656 x t) (@lem8038786 _142655 _142657 y u)). Qed.
Lemma lem8038790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038791 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term162 _142655 _142656 _142657 x t y u) = (term163 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038790) (@lem8038787 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038795 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038796 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term140 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (@lem8038795 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038798 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term141 _142655 _142657 y u) = (term48 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038797) (@lem8038796 _142655 _142657 y u)). Qed.
Lemma lem8038801 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term58 _142655 _142656 _142657 x t y u) = (term58 _142655 _142656 _142657 x t y u).
Proof. exact (eq_refl (term58 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038802 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term152 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038798 _142655 _142657 y u) (@lem8038801 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038805 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)) = ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)).
Proof. exact (MK_COMB (@lem8038791 _142655 _142656 _142657 x t y u) (@lem8038802 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038808 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u)).
Proof. exact (SYM (@lem8038805 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038809 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : term126 _142655 _142656 x t.
Proof. exact (@lem9851 (@IN (cart _142655 _142656) x t)). Qed.
Lemma lem8038810 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term126 _142655 _142656 x t) = (term127 _142655 _142656 x t).
Proof. exact (eq_refl (term126 _142655 _142656 x t)). Qed.
Lemma lem8038811 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : term127 _142655 _142656 x t.
Proof. exact (EQ_MP (@lem8038810 _142655 _142656 x t) (@lem8038809 _142655 _142656 x t)). Qed.
Lemma lem8038812 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = True) : (@IN (cart _142655 _142656) x t) = True.
Proof. exact (h1). Qed.
Lemma lem8038813 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = False) : (@IN (cart _142655 _142656) x t) = False.
Proof. exact (h1). Qed.
Lemma lem8038824 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term165 _142655 _142657 y u) = (term165 _142655 _142657 y u).
Proof. exact (eq_refl (term165 _142655 _142657 y u)). Qed.
Lemma lem8038825 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = True) : (term166 _142655 _142656 _142657 y u x t) = (term167 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038824 _142655 _142657 y u) (@lem8038812 _142655 _142656 x t h1)). Qed.
Lemma lem8038826 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term167 _142655 _142657 y u) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)).
Proof. exact (eq_refl (term167 _142655 _142657 y u)). Qed.
Lemma lem8038827 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term170 _142655 _142656 _142657 y u x t) = (term170 _142655 _142656 _142657 y u x t).
Proof. exact (eq_refl (term170 _142655 _142656 _142657 y u x t)). Qed.
Lemma lem8038828 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = (term167 _142655 _142657 y u)) = ((term166 _142655 _142656 _142657 y u x t) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u))).
Proof. exact (MK_COMB (@lem8038827 _142655 _142656 _142657 y u x t) (@lem8038826 _142655 _142657 y u)). Qed.
Lemma lem8038829 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term166 _142655 _142656 _142657 y u x t) = ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl (term166 _142655 _142656 _142657 y u x t)). Qed.
Lemma lem8038830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038831 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term170 _142655 _142656 _142657 y u x t) = (term171 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038830) (@lem8038829 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038832 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)).
Proof. exact (eq_refl ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u))). Qed.
Lemma lem8038833 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u))) = (((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u))).
Proof. exact (MK_COMB (@lem8038831 _142655 _142656 _142657 x t y u) (@lem8038832 _142655 _142657 y u)). Qed.
Lemma lem8038834 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = (term167 _142655 _142657 y u)) = (((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u))).
Proof. exact (TRANS (@lem8038828 _142655 _142656 _142657 x t y u) (@lem8038833 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038835 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = True) : ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)).
Proof. exact (EQ_MP (@lem8038834 _142655 _142656 _142657 x t y u) (@lem8038825 _142655 _142656 _142657 y u x t h1)). Qed.
Lemma lem8038836 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = True) : ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)) = ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)).
Proof. exact (SYM (@lem8038835 _142655 _142656 _142657 y u x t h1)). Qed.
Lemma lem8038837 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term165 _142655 _142657 y u) = (term165 _142655 _142657 y u).
Proof. exact (eq_refl (term165 _142655 _142657 y u)). Qed.
Lemma lem8038838 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = False) : (term166 _142655 _142656 _142657 y u x t) = (term172 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038837 _142655 _142657 y u) (@lem8038813 _142655 _142656 x t h1)). Qed.
Lemma lem8038839 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term172 _142655 _142657 y u) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)).
Proof. exact (eq_refl (term172 _142655 _142657 y u)). Qed.
Lemma lem8038840 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term170 _142655 _142656 _142657 y u x t) = (term170 _142655 _142656 _142657 y u x t).
Proof. exact (eq_refl (term170 _142655 _142656 _142657 y u x t)). Qed.
Lemma lem8038841 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = (term172 _142655 _142657 y u)) = ((term166 _142655 _142656 _142657 y u x t) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u))).
Proof. exact (MK_COMB (@lem8038840 _142655 _142656 _142657 y u x t) (@lem8038839 _142655 _142657 y u)). Qed.
Lemma lem8038842 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term166 _142655 _142656 _142657 y u x t) = ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)).
Proof. exact (eq_refl (term166 _142655 _142656 _142657 y u x t)). Qed.
Lemma lem8038843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038844 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term170 _142655 _142656 _142657 y u x t) = (term171 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8038843) (@lem8038842 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038845 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)).
Proof. exact (eq_refl ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u))). Qed.
Lemma lem8038846 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u))) = (((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u))).
Proof. exact (MK_COMB (@lem8038844 _142655 _142656 _142657 x t y u) (@lem8038845 _142655 _142657 y u)). Qed.
Lemma lem8038847 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term166 _142655 _142656 _142657 y u x t) = (term172 _142655 _142657 y u)) = (((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u))).
Proof. exact (TRANS (@lem8038841 _142655 _142656 _142657 x t y u) (@lem8038846 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038848 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = False) : ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)) = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)).
Proof. exact (EQ_MP (@lem8038847 _142655 _142656 _142657 x t y u) (@lem8038838 _142655 _142656 _142657 y u x t h1)). Qed.
Lemma lem8038849 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = False) : ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)) = ((term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u)).
Proof. exact (SYM (@lem8038848 _142655 _142656 _142657 y u x t h1)). Qed.
Lemma lem8038855 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8038856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038857 : term175 = (and False).
Proof. exact (MK_COMB (@lem8038856) (@lem8038855)). Qed.
Lemma lem8038858 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (eq_refl (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038859 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term168 _142655 _142657 y u) = (term145 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038857) (@lem8038858 _142655 _142657 y u)). Qed.
Lemma lem8038861 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038862 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term145 _142655 _142657 y u) = False.
Proof. exact (@lem8038861 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038863 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term168 _142655 _142657 y u) = False.
Proof. exact (TRANS (@lem8038859 _142655 _142657 y u) (@lem8038862 _142655 _142657 y u)). Qed.
Lemma lem8038864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038865 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term176 _142655 _142657 y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8038864) (@lem8038863 _142655 _142657 y u)). Qed.
Lemma lem8038869 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038870 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term140 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (@lem8038869 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038872 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term142 _142655 _142657 y u) = (term143 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038871) (@lem8038870 _142655 _142657 y u)). Qed.
Lemma lem8038873 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term48 _142655 _142657 y u) = (term48 _142655 _142657 y u).
Proof. exact (eq_refl (term48 _142655 _142657 y u)). Qed.
Lemma lem8038874 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term169 _142655 _142657 y u) = (term177 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038873 _142655 _142657 y u) (@lem8038872 _142655 _142657 y u)). Qed.
Lemma lem8038877 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)) = (False = (term177 _142655 _142657 y u)).
Proof. exact (MK_COMB (@lem8038865 _142655 _142657 y u) (@lem8038874 _142655 _142657 y u)). Qed.
Lemma lem8038879 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8038880 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (False = (term177 _142655 _142657 y u)) = (term178 _142655 _142657 y u).
Proof. exact (@lem8038879 (term177 _142655 _142657 y u)). Qed.
Lemma lem8038883 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)) = (term178 _142655 _142657 y u).
Proof. exact (TRANS (@lem8038877 _142655 _142657 y u) (@lem8038880 _142655 _142657 y u)). Qed.
Lemma lem8038884 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term178 _142655 _142657 y u) = ((term168 _142655 _142657 y u) = (term169 _142655 _142657 y u)).
Proof. exact (SYM (@lem8038883 _142655 _142657 y u)). Qed.
Lemma lem8038885 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : term126 _142655 _142657 y u.
Proof. exact (@lem9851 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038886 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term126 _142655 _142657 y u) = (term127 _142655 _142657 y u).
Proof. exact (eq_refl (term126 _142655 _142657 y u)). Qed.
Lemma lem8038887 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : term127 _142655 _142657 y u.
Proof. exact (EQ_MP (@lem8038886 _142655 _142657 y u) (@lem8038885 _142655 _142657 y u)). Qed.
Lemma lem8038888 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = True) : (@IN (cart _142655 _142657) y u) = True.
Proof. exact (h1). Qed.
Lemma lem8038889 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = False) : (@IN (cart _142655 _142657) y u) = False.
Proof. exact (h1). Qed.
Lemma lem8038894 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem8038895 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = True) : (term180 _142655 _142657 y u) = term181.
Proof. exact (MK_COMB (@lem8038894) (@lem8038888 _142655 _142657 y u h1)). Qed.
Lemma lem8038896 : term181 = term182.
Proof. exact (eq_refl term181). Qed.
Lemma lem8038897 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term183 _142655 _142657 y u) = (term183 _142655 _142657 y u).
Proof. exact (eq_refl (term183 _142655 _142657 y u)). Qed.
Lemma lem8038898 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term181) = ((term180 _142655 _142657 y u) = term182).
Proof. exact (MK_COMB (@lem8038897 _142655 _142657 y u) (@lem8038896)). Qed.
Lemma lem8038899 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term180 _142655 _142657 y u) = (term178 _142655 _142657 y u).
Proof. exact (eq_refl (term180 _142655 _142657 y u)). Qed.
Lemma lem8038900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038901 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term183 _142655 _142657 y u) = (term184 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038900) (@lem8038899 _142655 _142657 y u)). Qed.
Lemma lem8038902 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem8038903 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term182) = ((term178 _142655 _142657 y u) = term182).
Proof. exact (MK_COMB (@lem8038901 _142655 _142657 y u) (@lem8038902)). Qed.
Lemma lem8038904 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term181) = ((term178 _142655 _142657 y u) = term182).
Proof. exact (TRANS (@lem8038898 _142655 _142657 y u) (@lem8038903 _142655 _142657 y u)). Qed.
Lemma lem8038905 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = True) : (term178 _142655 _142657 y u) = term182.
Proof. exact (EQ_MP (@lem8038904 _142655 _142657 y u) (@lem8038895 _142655 _142657 y u h1)). Qed.
Lemma lem8038906 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = True) : term182 = (term178 _142655 _142657 y u).
Proof. exact (SYM (@lem8038905 _142655 _142657 y u h1)). Qed.
Lemma lem8038907 : term179 = term179.
Proof. exact (eq_refl term179). Qed.
Lemma lem8038908 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = False) : (term180 _142655 _142657 y u) = term185.
Proof. exact (MK_COMB (@lem8038907) (@lem8038889 _142655 _142657 y u h1)). Qed.
Lemma lem8038909 : term185 = term186.
Proof. exact (eq_refl term185). Qed.
Lemma lem8038910 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term183 _142655 _142657 y u) = (term183 _142655 _142657 y u).
Proof. exact (eq_refl (term183 _142655 _142657 y u)). Qed.
Lemma lem8038911 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term185) = ((term180 _142655 _142657 y u) = term186).
Proof. exact (MK_COMB (@lem8038910 _142655 _142657 y u) (@lem8038909)). Qed.
Lemma lem8038912 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term180 _142655 _142657 y u) = (term178 _142655 _142657 y u).
Proof. exact (eq_refl (term180 _142655 _142657 y u)). Qed.
Lemma lem8038913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038914 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term183 _142655 _142657 y u) = (term184 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038913) (@lem8038912 _142655 _142657 y u)). Qed.
Lemma lem8038915 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem8038916 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term186) = ((term178 _142655 _142657 y u) = term186).
Proof. exact (MK_COMB (@lem8038914 _142655 _142657 y u) (@lem8038915)). Qed.
Lemma lem8038917 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term180 _142655 _142657 y u) = term185) = ((term178 _142655 _142657 y u) = term186).
Proof. exact (TRANS (@lem8038911 _142655 _142657 y u) (@lem8038916 _142655 _142657 y u)). Qed.
Lemma lem8038918 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = False) : (term178 _142655 _142657 y u) = term186.
Proof. exact (EQ_MP (@lem8038917 _142655 _142657 y u) (@lem8038908 _142655 _142657 y u h1)). Qed.
Lemma lem8038919 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = False) : term186 = (term178 _142655 _142657 y u).
Proof. exact (SYM (@lem8038918 _142655 _142657 y u h1)). Qed.
Lemma lem8038921 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038922 : term187 = (~ True).
Proof. exact (@lem8038921 (~ True)). Qed.
Lemma lem8038924 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem8038925 : term187 = False.
Proof. exact (TRANS (@lem8038922) (@lem8038924)). Qed.
Lemma lem8038926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038927 : term182 = (~ False).
Proof. exact (MK_COMB (@lem8038926) (@lem8038925)). Qed.
Lemma lem8038929 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038930 : term182 = True.
Proof. exact (TRANS (@lem8038927) (@lem8038929)). Qed.
Lemma lem8038931 : True = term182.
Proof. exact (SYM (@lem8038930)). Qed.
Lemma lem8038932 : term182.
Proof. exact (EQ_MP (@lem8038931) (@lem0)). Qed.
Lemma lem8038934 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038935 : term188 = False.
Proof. exact (@lem8038934 (~ False)). Qed.
Lemma lem8038936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038937 : term186 = (~ False).
Proof. exact (MK_COMB (@lem8038936) (@lem8038935)). Qed.
Lemma lem8038939 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038940 : term186 = True.
Proof. exact (TRANS (@lem8038937) (@lem8038939)). Qed.
Lemma lem8038941 : True = term186.
Proof. exact (SYM (@lem8038940)). Qed.
Lemma lem8038942 : term186.
Proof. exact (EQ_MP (@lem8038941) (@lem0)). Qed.
Lemma lem8038943 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = False) : term178 _142655 _142657 y u.
Proof. exact (EQ_MP (@lem8038919 _142655 _142657 y u h1) (@lem8038942)). Qed.
Lemma lem8038944 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (h1 : (@IN (cart _142655 _142657) y u) = True) : term178 _142655 _142657 y u.
Proof. exact (EQ_MP (@lem8038906 _142655 _142657 y u h1) (@lem8038932)). Qed.
Lemma lem8038946 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : term178 _142655 _142657 y u.
Proof. exact (or_elim (@lem8038887 _142655 _142657 y u) (fun h0 : (@IN (cart _142655 _142657) y u) = True => @lem8038944 _142655 _142657 y u h0) (fun h0 : (@IN (cart _142655 _142657) y u) = False => @lem8038943 _142655 _142657 y u h0)). Qed.
Lemma lem8038947 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term168 _142655 _142657 y u) = (term169 _142655 _142657 y u).
Proof. exact (EQ_MP (@lem8038884 _142655 _142657 y u) (@lem8038946 _142655 _142657 y u)). Qed.
Lemma lem8038953 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8038955 : term189 = (and True).
Proof. exact (MK_COMB (@lem8038954) (@lem8038953)). Qed.
Lemma lem8038956 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (eq_refl (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038957 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term173 _142655 _142657 y u) = (term140 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038955) (@lem8038956 _142655 _142657 y u)). Qed.
Lemma lem8038959 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8038960 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term140 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (@lem8038959 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038961 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term173 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (TRANS (@lem8038957 _142655 _142657 y u) (@lem8038960 _142655 _142657 y u)). Qed.
Lemma lem8038962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8038963 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term190 _142655 _142657 y u) = (term191 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038962) (@lem8038961 _142655 _142657 y u)). Qed.
Lemma lem8038967 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038968 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term145 _142655 _142657 y u) = False.
Proof. exact (@lem8038967 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038969 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8038970 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term147 _142655 _142657 y u) = (~ False).
Proof. exact (MK_COMB (@lem8038969) (@lem8038968 _142655 _142657 y u)). Qed.
Lemma lem8038972 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8038973 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term147 _142655 _142657 y u) = True.
Proof. exact (TRANS (@lem8038970 _142655 _142657 y u) (@lem8038972)). Qed.
Lemma lem8038974 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term48 _142655 _142657 y u) = (term48 _142655 _142657 y u).
Proof. exact (eq_refl (term48 _142655 _142657 y u)). Qed.
Lemma lem8038975 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term174 _142655 _142657 y u) = (term192 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8038974 _142655 _142657 y u) (@lem8038973 _142655 _142657 y u)). Qed.
Lemma lem8038977 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8038978 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term192 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (@lem8038977 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038979 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term174 _142655 _142657 y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (TRANS (@lem8038975 _142655 _142657 y u) (@lem8038978 _142655 _142657 y u)). Qed.
Lemma lem8038980 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)) = ((@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u)).
Proof. exact (MK_COMB (@lem8038963 _142655 _142657 y u) (@lem8038979 _142655 _142657 y u)). Qed.
Lemma lem8038982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8038983 (x : Prop) : (x = x) = True.
Proof. exact (@lem8038982 Prop x). Qed.
Lemma lem8038984 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u)) = True.
Proof. exact (@lem8038983 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8038985 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)) = True.
Proof. exact (TRANS (@lem8038980 _142655 _142657 y u) (@lem8038984 _142655 _142657 y u)). Qed.
Lemma lem8038986 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : True = ((term173 _142655 _142657 y u) = (term174 _142655 _142657 y u)).
Proof. exact (SYM (@lem8038985 _142655 _142657 y u)). Qed.
Lemma lem8038987 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term173 _142655 _142657 y u) = (term174 _142655 _142657 y u).
Proof. exact (EQ_MP (@lem8038986 _142655 _142657 y u) (@lem0)). Qed.
Lemma lem8038988 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = False) : (term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u).
Proof. exact (EQ_MP (@lem8038849 _142655 _142656 _142657 y u x t h1) (@lem8038987 _142655 _142657 y u)). Qed.
Lemma lem8038989 {_142655 _142656 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (t : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x t) = True) : (term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u).
Proof. exact (EQ_MP (@lem8038836 _142655 _142656 _142657 y u x t h1) (@lem8038947 _142655 _142657 y u)). Qed.
Lemma lem8038991 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term161 _142655 _142656 _142657 x t y u) = (term164 _142655 _142656 _142657 x t y u).
Proof. exact (or_elim (@lem8038811 _142655 _142656 x t) (fun h0 : (@IN (cart _142655 _142656) x t) = True => @lem8038989 _142655 _142656 _142657 y u x t h0) (fun h0 : (@IN (cart _142655 _142656) x t) = False => @lem8038988 _142655 _142656 _142657 y u x t h0)). Qed.
Lemma lem8038992 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term151 _142655 _142656 _142657 x t y u) = (term152 _142655 _142656 _142657 x t y u).
Proof. exact (EQ_MP (@lem8038808 _142655 _142656 _142657 x t y u) (@lem8038991 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8038998 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8038999 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term193 _142655 _142656 x t) = False.
Proof. exact (@lem8038998 (term143 _142655 _142656 x t)). Qed.
Lemma lem8039000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039001 {_142655 _142656 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) : (term194 _142655 _142656 x t) = (and False).
Proof. exact (MK_COMB (@lem8039000) (@lem8038999 _142655 _142656 x t)). Qed.
Lemma lem8039002 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (@IN (cart _142655 _142657) y u) = (@IN (cart _142655 _142657) y u).
Proof. exact (eq_refl (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8039003 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term156 _142655 _142656 _142657 x t y u) = (term145 _142655 _142657 y u).
Proof. exact (MK_COMB (@lem8039001 _142655 _142656 x t) (@lem8039002 _142655 _142657 y u)). Qed.
Lemma lem8039005 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039006 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term145 _142655 _142657 y u) = False.
Proof. exact (@lem8039005 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8039007 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term156 _142655 _142656 _142657 x t y u) = False.
Proof. exact (TRANS (@lem8039003 _142655 _142656 _142657 x t y u) (@lem8039006 _142655 _142657 y u)). Qed.
Lemma lem8039008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8039009 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term195 _142655 _142656 _142657 x t y u) = (@eq Prop False).
Proof. exact (MK_COMB (@lem8039008) (@lem8039007 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039013 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039014 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term145 _142655 _142657 y u) = False.
Proof. exact (@lem8039013 (@IN (cart _142655 _142657) y u)). Qed.
Lemma lem8039015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8039016 {_142655 _142657 : Type'} (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term146 _142655 _142657 y u) = (and False).
Proof. exact (MK_COMB (@lem8039015) (@lem8039014 _142655 _142657 y u)). Qed.
Lemma lem8039019 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term58 _142655 _142656 _142657 x t y u) = (term58 _142655 _142656 _142657 x t y u).
Proof. exact (eq_refl (term58 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039020 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term157 _142655 _142656 _142657 x t y u) = (term196 _142655 _142656 _142657 x t y u).
Proof. exact (MK_COMB (@lem8039016 _142655 _142657 y u) (@lem8039019 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039022 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem8039023 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term196 _142655 _142656 _142657 x t y u) = False.
Proof. exact (@lem8039022 (term58 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039024 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term157 _142655 _142656 _142657 x t y u) = False.
Proof. exact (TRANS (@lem8039020 _142655 _142656 _142657 x t y u) (@lem8039023 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039025 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)) = (False = False).
Proof. exact (MK_COMB (@lem8039009 _142655 _142656 _142657 x t y u) (@lem8039024 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039027 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem8039028 : (False = False) = (~ False).
Proof. exact (@lem8039027 False). Qed.
Lemma lem8039030 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem8039031 : (False = False) = True.
Proof. exact (TRANS (@lem8039028) (@lem8039030)). Qed.
Lemma lem8039032 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)) = True.
Proof. exact (TRANS (@lem8039025 _142655 _142656 _142657 x t y u) (@lem8039031)). Qed.
Lemma lem8039033 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : True = ((term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u)).
Proof. exact (SYM (@lem8039032 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039034 {_142655 _142656 _142657 : Type'} (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term156 _142655 _142656 _142657 x t y u) = (term157 _142655 _142656 _142657 x t y u).
Proof. exact (EQ_MP (@lem8039033 _142655 _142656 _142657 x t y u) (@lem0)). Qed.
Lemma lem8039035 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = False) : (term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u).
Proof. exact (EQ_MP (@lem8038776 _142655 _142656 _142657 t y u x s h1) (@lem8039034 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039036 {_142655 _142656 _142657 : Type'} (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) (x : cart _142655 _142656) (s : type24 _142655 _142656) (h1 : (@IN (cart _142655 _142656) x s) = True) : (term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u).
Proof. exact (EQ_MP (@lem8038763 _142655 _142656 _142657 t y u x s h1) (@lem8038992 _142655 _142656 _142657 x t y u)). Qed.
Lemma lem8039039 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (y : cart _142655 _142657) (u : type24 _142655 _142657) : (term103 _142655 _142656 _142657 s x t y u) = (term107 _142655 _142656 _142657 s x t y u).
Proof. exact (or_elim (@lem8038734 _142655 _142656 x s) (fun h0 : (@IN (cart _142655 _142656) x s) = True => @lem8039036 _142655 _142656 _142657 t y u x s h0) (fun h0 : (@IN (cart _142655 _142656) x s) = False => @lem8039035 _142655 _142656 _142657 t y u x s h0)). Qed.
Lemma lem8039044 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (x : cart _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : term109 _142655 _142656 _142657 s x t u.
Proof. exact (fun y : cart _142655 _142657 => @lem8039039 _142655 _142656 _142657 s x t y u). Qed.
Lemma lem8039049 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) (u : type24 _142655 _142657) : term111 _142655 _142656 _142657 s t u.
Proof. exact (fun x : cart _142655 _142656 => @lem8039044 _142655 _142656 _142657 s x t u). Qed.
Lemma lem8039054 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) (t : type24 _142655 _142656) : term115 _142655 _142656 _142657 s t.
Proof. exact (fun u : type24 _142655 _142657 => @lem8039049 _142655 _142656 _142657 s t u). Qed.
Lemma lem8039059 {_142655 _142656 _142657 : Type'} (s : type24 _142655 _142656) : term119 _142655 _142656 _142657 s.
Proof. exact (fun t : type24 _142655 _142656 => @lem8039054 _142655 _142656 _142657 s t). Qed.
Lemma lem8039064 {_142655 _142656 _142657 : Type'} : term123 _142655 _142656 _142657.
Proof. exact (fun s : type24 _142655 _142656 => @lem8039059 _142655 _142656 _142657 s). Qed.
Lemma lem8039069 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (x : cart _142619 _142620) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : term61 _142619 _142620 _142621 t x s u.
Proof. exact (fun y : cart _142619 _142621 => @lem8038717 _142619 _142620 _142621 t x s y u). Qed.
Lemma lem8039074 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) (u : type24 _142619 _142621) : term63 _142619 _142620 _142621 t s u.
Proof. exact (fun x : cart _142619 _142620 => @lem8039069 _142619 _142620 _142621 t x s u). Qed.
Lemma lem8039079 {_142619 _142620 _142621 : Type'} (t : type24 _142619 _142621) (s : type24 _142619 _142620) : term67 _142619 _142620 _142621 t s.
Proof. exact (fun u : type24 _142619 _142621 => @lem8039074 _142619 _142620 _142621 t s u). Qed.
Lemma lem8039084 {_142619 _142620 _142621 : Type'} (s : type24 _142619 _142620) : term71 _142619 _142620 _142621 s.
Proof. exact (fun t : type24 _142619 _142621 => @lem8039079 _142619 _142620 _142621 t s). Qed.
Lemma lem8039089 {_142619 _142620 _142621 : Type'} : term75 _142619 _142620 _142621.
Proof. exact (fun s : type24 _142619 _142620 => @lem8039084 _142619 _142620 _142621 s). Qed.
Lemma lem8039090 {_142619 _142620 _142621 _142655 _142656 _142657 : Type'} : term125 _142619 _142620 _142621 _142655 _142656 _142657.
Proof. exact (conj (@lem8039089 _142619 _142620 _142621) (@lem8039064 _142655 _142656 _142657)). Qed.
Lemma lem8039091 {_142619 _142620 _142621 _142655 _142656 _142657 : Type'} : term124 _142619 _142620 _142621 _142655 _142656 _142657.
Proof. exact (EQ_MP (@lem8038584 _142619 _142620 _142621 _142655 _142656 _142657) (@lem8039090 _142619 _142620 _142621 _142655 _142656 _142657)). Qed.
