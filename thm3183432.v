Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183432_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183071_spec.
Require Import thm3183072_spec.
Lemma lem3183348 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem3183072 A B f g) (@lem3183071 A B f g)). Qed.
Lemma lem3183349 {_83123 : Type'} (f : type1538 _83123) (g : type1538 _83123) : (f = g) = (term1 _83123 f g).
Proof. exact (@lem3183348 Prop (_83123 -> Prop) f g). Qed.
Lemma lem3183350 {_83123 : Type'} (x : _83123) : ((@SETSPEC _83123 x) = (term2 _83123 x)) = (term3 _83123 x).
Proof. exact (@lem3183349 _83123 (@SETSPEC _83123 x) (term2 _83123 x)). Qed.
Lemma lem3183358 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem3183072 A B f g) (@lem3183071 A B f g)). Qed.
Lemma lem3183359 {_83123 : Type'} (f : _83123 -> Prop) (g : _83123 -> Prop) : (f = g) = (term4 _83123 f g).
Proof. exact (@lem3183358 _83123 Prop f g). Qed.
Lemma lem3183360 {_83123 : Type'} (x : _83123) (x' : Prop) : ((@SETSPEC _83123 x x') = (term5 _83123 x x')) = (term6 _83123 x x').
Proof. exact (@lem3183359 _83123 (@SETSPEC _83123 x x') (term5 _83123 x x')). Qed.
Lemma lem3183370 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183371 {_83123 : Type'} (f : type1538 _83123) (y : Prop) : (term8 _83123 f y) = (f y).
Proof. exact (@lem3183370 Prop (_83123 -> Prop) f y). Qed.
Lemma lem3183372 {_83123 : Type'} (x : _83123) (x' : Prop) : (term9 _83123 x x') = (term5 _83123 x x').
Proof. exact (@lem3183371 _83123 (term2 _83123 x) x'). Qed.
Lemma lem3183373 {_83123 : Type'} (p : Prop) (x : _83123) : (term5 _83123 x p) = (term10 _83123 p x).
Proof. exact (eq_refl (term5 _83123 x p)). Qed.
Lemma lem3183374 {_83123 : Type'} (x : _83123) : (term11 _83123 x) = (term2 _83123 x).
Proof. exact (fun_ext (fun p : Prop => @lem3183373 _83123 p x)). Qed.
Lemma lem3183375 (x : Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183376 {_83123 : Type'} (x : _83123) (x' : Prop) : (term9 _83123 x x') = (term5 _83123 x x').
Proof. exact (MK_COMB (@lem3183374 _83123 x) (@lem3183375 x')). Qed.
Lemma lem3183377 {_83123 : Type'} : (@eq (_83123 -> Prop)) = (@eq (_83123 -> Prop)).
Proof. exact (eq_refl (@eq (_83123 -> Prop))). Qed.
Lemma lem3183378 {_83123 : Type'} (x : _83123) (x' : Prop) : (term12 _83123 x x') = (term13 _83123 x x').
Proof. exact (MK_COMB (@lem3183377 _83123) (@lem3183376 _83123 x x')). Qed.
Lemma lem3183379 {_83123 : Type'} (x : Prop) (x' : _83123) : (term5 _83123 x' x) = (term10 _83123 x x').
Proof. exact (eq_refl (term5 _83123 x' x)). Qed.
Lemma lem3183380 {_83123 : Type'} (x : Prop) (x' : _83123) : ((term9 _83123 x' x) = (term5 _83123 x' x)) = ((term5 _83123 x' x) = (term10 _83123 x x')).
Proof. exact (MK_COMB (@lem3183378 _83123 x' x) (@lem3183379 _83123 x x')). Qed.
Lemma lem3183381 {_83123 : Type'} (x : Prop) (x' : _83123) : (term5 _83123 x' x) = (term10 _83123 x x').
Proof. exact (EQ_MP (@lem3183380 _83123 x x') (@lem3183372 _83123 x' x)). Qed.
Lemma lem3183388 {_83123 : Type'} (x' : _83123) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3183389 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term14 _83123 x' x x'') = (term15 _83123 x x' x'').
Proof. exact (MK_COMB (@lem3183381 _83123 x x') (@lem3183388 _83123 x'')). Qed.
Lemma lem3183391 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183392 {_83123 : Type'} (f : _83123 -> Prop) (y : _83123) : (term16 _83123 f y) = (f y).
Proof. exact (@lem3183391 _83123 Prop f y). Qed.
Lemma lem3183393 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term17 _83123 x x' x'') = (term15 _83123 x x' x'').
Proof. exact (@lem3183392 _83123 (term10 _83123 x x') x''). Qed.
Lemma lem3183394 {_83123 : Type'} (x : Prop) (x' : _83123) (t : _83123) : (term15 _83123 x x' t) = (term18 _83123 x x' t).
Proof. exact (eq_refl (term15 _83123 x x' t)). Qed.
Lemma lem3183395 {_83123 : Type'} (x : Prop) (x' : _83123) : (term19 _83123 x x') = (term10 _83123 x x').
Proof. exact (fun_ext (fun t : _83123 => @lem3183394 _83123 x x' t)). Qed.
Lemma lem3183396 {_83123 : Type'} (x' : _83123) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3183397 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term17 _83123 x x' x'') = (term15 _83123 x x' x'').
Proof. exact (MK_COMB (@lem3183395 _83123 x x') (@lem3183396 _83123 x'')). Qed.
Lemma lem3183398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183399 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term20 _83123 x x' x'') = (term21 _83123 x x' x'').
Proof. exact (MK_COMB (@lem3183398) (@lem3183397 _83123 x x' x'')). Qed.
Lemma lem3183400 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term15 _83123 x x' x'') = (term18 _83123 x x' x'').
Proof. exact (eq_refl (term15 _83123 x x' x'')). Qed.
Lemma lem3183401 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : ((term17 _83123 x x' x'') = (term15 _83123 x x' x'')) = ((term15 _83123 x x' x'') = (term18 _83123 x x' x'')).
Proof. exact (MK_COMB (@lem3183399 _83123 x x' x'') (@lem3183400 _83123 x x' x'')). Qed.
Lemma lem3183402 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term15 _83123 x x' x'') = (term18 _83123 x x' x'').
Proof. exact (EQ_MP (@lem3183401 _83123 x x' x'') (@lem3183393 _83123 x x' x'')). Qed.
Lemma lem3183409 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : (term14 _83123 x' x x'') = (term18 _83123 x x' x'').
Proof. exact (TRANS (@lem3183389 _83123 x x' x'') (@lem3183402 _83123 x x' x'')). Qed.
Lemma lem3183410 {_83123 : Type'} (x : _83123) (x' : Prop) (x'' : _83123) : (term22 _83123 x x' x'') = (term22 _83123 x x' x'').
Proof. exact (eq_refl (term22 _83123 x x' x'')). Qed.
Lemma lem3183411 {_83123 : Type'} (x : Prop) (x' : _83123) (x'' : _83123) : ((@SETSPEC _83123 x' x x'') = (term14 _83123 x' x x'')) = ((@SETSPEC _83123 x' x x'') = (term18 _83123 x x' x'')).
Proof. exact (MK_COMB (@lem3183410 _83123 x' x x'') (@lem3183409 _83123 x x' x'')). Qed.
Lemma lem3183416 {_83123 : Type'} (x : Prop) (x' : _83123) : (term23 _83123 x' x) = (term24 _83123 x x').
Proof. exact (fun_ext (fun x'' : _83123 => @lem3183411 _83123 x x' x'')). Qed.
Lemma lem3183417 {_83123 : Type'} : (@all _83123) = (@all _83123).
Proof. exact (eq_refl (@all _83123)). Qed.
Lemma lem3183418 {_83123 : Type'} (x : Prop) (x' : _83123) : (term6 _83123 x' x) = (term25 _83123 x x').
Proof. exact (MK_COMB (@lem3183417 _83123) (@lem3183416 _83123 x x')). Qed.
Lemma lem3183423 {_83123 : Type'} (x : Prop) (x' : _83123) : ((@SETSPEC _83123 x' x) = (term5 _83123 x' x)) = (term25 _83123 x x').
Proof. exact (TRANS (@lem3183360 _83123 x' x) (@lem3183418 _83123 x x')). Qed.
Lemma lem3183424 {_83123 : Type'} (x : _83123) : (term26 _83123 x) = (term27 _83123 x).
Proof. exact (fun_ext (fun x' : Prop => @lem3183423 _83123 x' x)). Qed.
Lemma lem3183425 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3183426 {_83123 : Type'} (x : _83123) : (term3 _83123 x) = (term28 _83123 x).
Proof. exact (MK_COMB (@lem3183425) (@lem3183424 _83123 x)). Qed.
Lemma lem3183431 {_83123 : Type'} (x : _83123) : ((@SETSPEC _83123 x) = (term2 _83123 x)) = (term28 _83123 x).
Proof. exact (TRANS (@lem3183350 _83123 x) (@lem3183426 _83123 x)). Qed.
Lemma lem3183432 {_83123 : Type'} (x : _83123) : (term28 _83123 x) = ((@SETSPEC _83123 x) = (term2 _83123 x)).
Proof. exact (SYM (@lem3183431 _83123 x)). Qed.
