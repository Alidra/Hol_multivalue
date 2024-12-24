Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183343_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3183071_spec.
Require Import thm3183072_spec.
Lemma lem3183259 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem3183072 A B f g) (@lem3183071 A B f g)). Qed.
Lemma lem3183260 {_83064 : Type'} (f : type1538 _83064) (g : type1538 _83064) : (f = g) = (term1 _83064 f g).
Proof. exact (@lem3183259 Prop (_83064 -> Prop) f g). Qed.
Lemma lem3183261 {_83064 : Type'} (x : _83064) : ((@SETSPEC _83064 x) = (term2 _83064 x)) = (term3 _83064 x).
Proof. exact (@lem3183260 _83064 (@SETSPEC _83064 x) (term2 _83064 x)). Qed.
Lemma lem3183269 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem3183072 A B f g) (@lem3183071 A B f g)). Qed.
Lemma lem3183270 {_83064 : Type'} (f : _83064 -> Prop) (g : _83064 -> Prop) : (f = g) = (term4 _83064 f g).
Proof. exact (@lem3183269 _83064 Prop f g). Qed.
Lemma lem3183271 {_83064 : Type'} (x : _83064) (x' : Prop) : ((@SETSPEC _83064 x x') = (term5 _83064 x x')) = (term6 _83064 x x').
Proof. exact (@lem3183270 _83064 (@SETSPEC _83064 x x') (term5 _83064 x x')). Qed.
Lemma lem3183281 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183282 {_83064 : Type'} (f : type1538 _83064) (y : Prop) : (term8 _83064 f y) = (f y).
Proof. exact (@lem3183281 Prop (_83064 -> Prop) f y). Qed.
Lemma lem3183283 {_83064 : Type'} (x : _83064) (x' : Prop) : (term9 _83064 x x') = (term5 _83064 x x').
Proof. exact (@lem3183282 _83064 (term2 _83064 x) x'). Qed.
Lemma lem3183284 {_83064 : Type'} (p : Prop) (x : _83064) : (term5 _83064 x p) = (term10 _83064 p x).
Proof. exact (eq_refl (term5 _83064 x p)). Qed.
Lemma lem3183285 {_83064 : Type'} (x : _83064) : (term11 _83064 x) = (term2 _83064 x).
Proof. exact (fun_ext (fun p : Prop => @lem3183284 _83064 p x)). Qed.
Lemma lem3183286 (x : Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3183287 {_83064 : Type'} (x : _83064) (x' : Prop) : (term9 _83064 x x') = (term5 _83064 x x').
Proof. exact (MK_COMB (@lem3183285 _83064 x) (@lem3183286 x')). Qed.
Lemma lem3183288 {_83064 : Type'} : (@eq (_83064 -> Prop)) = (@eq (_83064 -> Prop)).
Proof. exact (eq_refl (@eq (_83064 -> Prop))). Qed.
Lemma lem3183289 {_83064 : Type'} (x : _83064) (x' : Prop) : (term12 _83064 x x') = (term13 _83064 x x').
Proof. exact (MK_COMB (@lem3183288 _83064) (@lem3183287 _83064 x x')). Qed.
Lemma lem3183290 {_83064 : Type'} (x : Prop) (x' : _83064) : (term5 _83064 x' x) = (term10 _83064 x x').
Proof. exact (eq_refl (term5 _83064 x' x)). Qed.
Lemma lem3183291 {_83064 : Type'} (x : Prop) (x' : _83064) : ((term9 _83064 x' x) = (term5 _83064 x' x)) = ((term5 _83064 x' x) = (term10 _83064 x x')).
Proof. exact (MK_COMB (@lem3183289 _83064 x' x) (@lem3183290 _83064 x x')). Qed.
Lemma lem3183292 {_83064 : Type'} (x : Prop) (x' : _83064) : (term5 _83064 x' x) = (term10 _83064 x x').
Proof. exact (EQ_MP (@lem3183291 _83064 x x') (@lem3183283 _83064 x' x)). Qed.
Lemma lem3183299 {_83064 : Type'} (x' : _83064) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3183300 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term14 _83064 x' x x'') = (term15 _83064 x x' x'').
Proof. exact (MK_COMB (@lem3183292 _83064 x x') (@lem3183299 _83064 x'')). Qed.
Lemma lem3183302 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3183303 {_83064 : Type'} (f : _83064 -> Prop) (y : _83064) : (term16 _83064 f y) = (f y).
Proof. exact (@lem3183302 _83064 Prop f y). Qed.
Lemma lem3183304 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term17 _83064 x x' x'') = (term15 _83064 x x' x'').
Proof. exact (@lem3183303 _83064 (term10 _83064 x x') x''). Qed.
Lemma lem3183305 {_83064 : Type'} (x : Prop) (x' : _83064) (t : _83064) : (term15 _83064 x x' t) = (term18 _83064 x x' t).
Proof. exact (eq_refl (term15 _83064 x x' t)). Qed.
Lemma lem3183306 {_83064 : Type'} (x : Prop) (x' : _83064) : (term19 _83064 x x') = (term10 _83064 x x').
Proof. exact (fun_ext (fun t : _83064 => @lem3183305 _83064 x x' t)). Qed.
Lemma lem3183307 {_83064 : Type'} (x' : _83064) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3183308 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term17 _83064 x x' x'') = (term15 _83064 x x' x'').
Proof. exact (MK_COMB (@lem3183306 _83064 x x') (@lem3183307 _83064 x'')). Qed.
Lemma lem3183309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183310 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term20 _83064 x x' x'') = (term21 _83064 x x' x'').
Proof. exact (MK_COMB (@lem3183309) (@lem3183308 _83064 x x' x'')). Qed.
Lemma lem3183311 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term15 _83064 x x' x'') = (term18 _83064 x x' x'').
Proof. exact (eq_refl (term15 _83064 x x' x'')). Qed.
Lemma lem3183312 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : ((term17 _83064 x x' x'') = (term15 _83064 x x' x'')) = ((term15 _83064 x x' x'') = (term18 _83064 x x' x'')).
Proof. exact (MK_COMB (@lem3183310 _83064 x x' x'') (@lem3183311 _83064 x x' x'')). Qed.
Lemma lem3183313 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term15 _83064 x x' x'') = (term18 _83064 x x' x'').
Proof. exact (EQ_MP (@lem3183312 _83064 x x' x'') (@lem3183304 _83064 x x' x'')). Qed.
Lemma lem3183320 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : (term14 _83064 x' x x'') = (term18 _83064 x x' x'').
Proof. exact (TRANS (@lem3183300 _83064 x x' x'') (@lem3183313 _83064 x x' x'')). Qed.
Lemma lem3183321 {_83064 : Type'} (x : _83064) (x' : Prop) (x'' : _83064) : (term22 _83064 x x' x'') = (term22 _83064 x x' x'').
Proof. exact (eq_refl (term22 _83064 x x' x'')). Qed.
Lemma lem3183322 {_83064 : Type'} (x : Prop) (x' : _83064) (x'' : _83064) : ((@SETSPEC _83064 x' x x'') = (term14 _83064 x' x x'')) = ((@SETSPEC _83064 x' x x'') = (term18 _83064 x x' x'')).
Proof. exact (MK_COMB (@lem3183321 _83064 x' x x'') (@lem3183320 _83064 x x' x'')). Qed.
Lemma lem3183327 {_83064 : Type'} (x : Prop) (x' : _83064) : (term23 _83064 x' x) = (term24 _83064 x x').
Proof. exact (fun_ext (fun x'' : _83064 => @lem3183322 _83064 x x' x'')). Qed.
Lemma lem3183328 {_83064 : Type'} : (@all _83064) = (@all _83064).
Proof. exact (eq_refl (@all _83064)). Qed.
Lemma lem3183329 {_83064 : Type'} (x : Prop) (x' : _83064) : (term6 _83064 x' x) = (term25 _83064 x x').
Proof. exact (MK_COMB (@lem3183328 _83064) (@lem3183327 _83064 x x')). Qed.
Lemma lem3183334 {_83064 : Type'} (x : Prop) (x' : _83064) : ((@SETSPEC _83064 x' x) = (term5 _83064 x' x)) = (term25 _83064 x x').
Proof. exact (TRANS (@lem3183271 _83064 x' x) (@lem3183329 _83064 x x')). Qed.
Lemma lem3183335 {_83064 : Type'} (x : _83064) : (term26 _83064 x) = (term27 _83064 x).
Proof. exact (fun_ext (fun x' : Prop => @lem3183334 _83064 x' x)). Qed.
Lemma lem3183336 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3183337 {_83064 : Type'} (x : _83064) : (term3 _83064 x) = (term28 _83064 x).
Proof. exact (MK_COMB (@lem3183336) (@lem3183335 _83064 x)). Qed.
Lemma lem3183342 {_83064 : Type'} (x : _83064) : ((@SETSPEC _83064 x) = (term2 _83064 x)) = (term28 _83064 x).
Proof. exact (TRANS (@lem3183261 _83064 x) (@lem3183337 _83064 x)). Qed.
Lemma lem3183343 {_83064 : Type'} (x : _83064) : (term28 _83064 x) = ((@SETSPEC _83064 x) = (term2 _83064 x)).
Proof. exact (SYM (@lem3183342 _83064 x)). Qed.
