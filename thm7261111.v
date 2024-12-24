Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261111_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7260962_spec.
Lemma lem7261038 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term1 _137613 s f g x.
Proof. exact (@lem7260962 _137613 s f g h1 x). Qed.
Lemma lem7261039 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) : (term1 _137613 s f g x) = (term2 _137613 s f g x).
Proof. exact (eq_refl (term1 _137613 s f g x)). Qed.
Lemma lem7261040 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term2 _137613 s f g x.
Proof. exact (EQ_MP (@lem7261039 _137613 s f g x) (@lem7261038 _137613 x s f g h1)). Qed.
Lemma lem7261041 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (h1 : @IN _137613 x s) : @IN _137613 x s.
Proof. exact (h1). Qed.
Lemma lem7261042 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : (f x) = (g x).
Proof. exact (@lem7261040 _137613 x s f g h1 (@lem7261041 _137613 x s h2)). Qed.
Lemma lem7261055 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term3 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7261056 (p : Prop) (q : Prop) (p' : Prop) : term4 p q p'.
Proof. exact (fun q' : Prop => @lem7261055 p q p' q'). Qed.
Lemma lem7261057 (p : Prop) (q : Prop) : term5 p q.
Proof. exact (fun p' : Prop => @lem7261056 p q p'). Qed.
Lemma lem7261058 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) : term6 _137613 s f g x.
Proof. exact (@lem7261057 (@IN _137613 x s) ((term7 _137613 f x) = (g x))). Qed.
Lemma lem7261059 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) : term8 _137613 s f g x p'.
Proof. exact (@lem7261058 _137613 s f g x p'). Qed.
Lemma lem7261060 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) : (term8 _137613 s f g x p') = (term9 _137613 s f g x p').
Proof. exact (eq_refl (term8 _137613 s f g x p')). Qed.
Lemma lem7261061 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) : term9 _137613 s f g x p'.
Proof. exact (EQ_MP (@lem7261060 _137613 s f g x p') (@lem7261059 _137613 s f g x p')). Qed.
Lemma lem7261062 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) (q' : Prop) : term10 _137613 s f g x p' q'.
Proof. exact (@lem7261061 _137613 s f g x p' q'). Qed.
Lemma lem7261063 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) (q' : Prop) : (term10 _137613 s f g x p' q') = (term11 _137613 s f g x p' q').
Proof. exact (eq_refl (term10 _137613 s f g x p' q')). Qed.
Lemma lem7261064 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (p' : Prop) (q' : Prop) : term11 _137613 s f g x p' q'.
Proof. exact (EQ_MP (@lem7261063 _137613 s f g x p' q') (@lem7261062 _137613 s f g x p' q')). Qed.
Lemma lem7261065 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) : (@IN _137613 x s) = (@IN _137613 x s).
Proof. exact (eq_refl (@IN _137613 x s)). Qed.
Lemma lem7261066 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (q' : Prop) : term12 _137613 f g x s q'.
Proof. exact (@lem7261064 _137613 s f g x (@IN _137613 x s) q'). Qed.
Lemma lem7261067 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (q' : Prop) : term13 _137613 f g x s q'.
Proof. exact (@lem7261066 _137613 f g x s q' (@lem7261065 _137613 x s)). Qed.
Lemma lem7261068 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (h1 : @IN _137613 x s) : @IN _137613 x s.
Proof. exact (h1). Qed.
Lemma lem7261069 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) : (@IN _137613 x s) = ((@IN _137613 x s) = True).
Proof. exact (@lem7 (@IN _137613 x s)). Qed.
Lemma lem7261074 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7261075 {_137613 : Type'} (f : _137613 -> real) (y : _137613) : (term7 _137613 f y) = (f y).
Proof. exact (@lem7261074 _137613 real f y). Qed.
Lemma lem7261076 {_137613 : Type'} (f : _137613 -> real) (x : _137613) : (term7 _137613 f x) = (f x).
Proof. exact (@lem7261075 _137613 f x). Qed.
Lemma lem7261078 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term2 _137613 s f g x.
Proof. exact (fun h0 : @IN _137613 x s => @lem7261042 _137613 f g x s h1 h0). Qed.
Lemma lem7261079 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term2 _137613 s f g x.
Proof. exact (@lem7261078 _137613 x s f g h1). Qed.
Lemma lem7261081 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (h1 : @IN _137613 x s) : (@IN _137613 x s) = True.
Proof. exact (EQ_MP (@lem7261069 _137613 x s) (@lem7261068 _137613 x s h1)). Qed.
Lemma lem7261082 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (h1 : @IN _137613 x s) : True = (@IN _137613 x s).
Proof. exact (SYM (@lem7261081 _137613 x s h1)). Qed.
Lemma lem7261083 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (h1 : @IN _137613 x s) : @IN _137613 x s.
Proof. exact (EQ_MP (@lem7261082 _137613 x s h1) (@lem0)). Qed.
Lemma lem7261084 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : (f x) = (g x).
Proof. exact (@lem7261079 _137613 x s f g h1 (@lem7261083 _137613 x s h2)). Qed.
Lemma lem7261085 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : (term7 _137613 f x) = (g x).
Proof. exact (TRANS (@lem7261076 _137613 f x) (@lem7261084 _137613 f g x s h1 h2)). Qed.
Lemma lem7261086 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7261087 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : (term15 _137613 f x) = (term16 _137613 g x).
Proof. exact (MK_COMB (@lem7261086) (@lem7261085 _137613 f g x s h1 h2)). Qed.
Lemma lem7261088 {_137613 : Type'} (g : _137613 -> real) (x : _137613) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem7261089 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : ((term7 _137613 f x) = (g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem7261087 _137613 f g x s h1 h2) (@lem7261088 _137613 g x)). Qed.
Lemma lem7261091 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7261092 (x : real) : (x = x) = True.
Proof. exact (@lem7261091 real x). Qed.
Lemma lem7261093 {_137613 : Type'} (g : _137613 -> real) (x : _137613) : ((g x) = (g x)) = True.
Proof. exact (@lem7261092 (g x)). Qed.
Lemma lem7261094 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) (h1 : term0 _137613 s f g) (h2 : @IN _137613 x s) : ((term7 _137613 f x) = (g x)) = True.
Proof. exact (TRANS (@lem7261089 _137613 f g x s h1 h2) (@lem7261093 _137613 g x)). Qed.
Lemma lem7261095 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term17 _137613 s f g x.
Proof. exact (fun h0 : @IN _137613 x s => @lem7261094 _137613 f g x s h1 h0). Qed.
Lemma lem7261096 {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (x : _137613) (s : _137613 -> Prop) : term18 _137613 f g x s.
Proof. exact (@lem7261067 _137613 f g x s True). Qed.
Lemma lem7261097 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term19 _137613 s f g x) = (term20 _137613 x s).
Proof. exact (@lem7261096 _137613 f g x s (@lem7261095 _137613 x s f g h1)). Qed.
Lemma lem7261099 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7261100 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) : (term20 _137613 x s) = True.
Proof. exact (@lem7261099 (@IN _137613 x s)). Qed.
Lemma lem7261101 {_137613 : Type'} (x : _137613) (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term19 _137613 s f g x) = True.
Proof. exact (TRANS (@lem7261097 _137613 x s f g h1) (@lem7261100 _137613 x s)). Qed.
Lemma lem7261102 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term21 _137613 s f g) = (term22 _137613).
Proof. exact (fun_ext (fun x : _137613 => @lem7261101 _137613 x s f g h1)). Qed.
Lemma lem7261103 {_137613 : Type'} : (@all _137613) = (@all _137613).
Proof. exact (eq_refl (@all _137613)). Qed.
Lemma lem7261104 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term23 _137613 s f g) = (term24 _137613).
Proof. exact (MK_COMB (@lem7261103 _137613) (@lem7261102 _137613 s f g h1)). Qed.
Lemma lem7261106 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7261107 {_137613 : Type'} (t : Prop) : (term25 _137613 t) = t.
Proof. exact (@lem7261106 _137613 t). Qed.
Lemma lem7261108 {_137613 : Type'} : (term24 _137613) = True.
Proof. exact (@lem7261107 _137613 True). Qed.
Lemma lem7261109 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : (term23 _137613 s f g) = True.
Proof. exact (TRANS (@lem7261104 _137613 s f g h1) (@lem7261108 _137613)). Qed.
Lemma lem7261110 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : True = (term23 _137613 s f g).
Proof. exact (SYM (@lem7261109 _137613 s f g h1)). Qed.
Lemma lem7261111 {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : term0 _137613 s f g) : term23 _137613 s f g.
Proof. exact (EQ_MP (@lem7261110 _137613 s f g h1) (@lem0)). Qed.
