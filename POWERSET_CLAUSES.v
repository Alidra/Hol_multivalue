Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POWERSET_CLAUSES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNION_spec.
Require Import SING_GSPEC_spec.
Require Import SUBSET_spec.
Require Import SUBSET_ANTISYM_spec.
Require Import SUBSET_EMPTY_spec.
Require Import SUBSET_INSERT_DELETE_spec.
Require Import UNION_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17930_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem4606458 {A : Type'} (a : A) (s : A -> Prop) : term0 A a s.
Proof. exact (@lem9784 (@IN A a s)). Qed.
Lemma lem4606459 {A : Type'} (a : A) (s : A -> Prop) : (term0 A a s) = (term1 A a s).
Proof. exact (eq_refl (term0 A a s)). Qed.
Lemma lem4606460 {A : Type'} (a : A) (s : A -> Prop) : term1 A a s.
Proof. exact (EQ_MP (@lem4606459 A a s) (@lem4606458 A a s)). Qed.
Lemma lem4606461 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4606462 {A : Type'} (a : A) (s : A -> Prop) (h1 : term2 A a s) : term2 A a s.
Proof. exact (h1). Qed.
Lemma lem4606473 {A B : Type'} (y : B) : term3 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4606474 {A B : Type'} (y : B) : (term3 A B y) = (term4 A B y).
Proof. exact (eq_refl (term3 A B y)). Qed.
Lemma lem4606475 {A B : Type'} (y : B) : term4 A B y.
Proof. exact (EQ_MP (@lem4606474 A B y) (@lem4606473 A B y)). Qed.
Lemma lem4606476 {A B : Type'} (y : B) (s : A -> Prop) : term5 A B y s.
Proof. exact (@lem4606475 A B y s). Qed.
Lemma lem4606477 {A B : Type'} (y : B) (s : A -> Prop) : (term5 A B y s) = (term6 A B y s).
Proof. exact (eq_refl (term5 A B y s)). Qed.
Lemma lem4606478 {A B : Type'} (y : B) (s : A -> Prop) : term6 A B y s.
Proof. exact (EQ_MP (@lem4606477 A B y s) (@lem4606476 A B y s)). Qed.
Lemma lem4606479 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term7 A B y s f.
Proof. exact (@lem4606478 A B y s f). Qed.
Lemma lem4606480 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term7 A B y s f) = ((term8 A B y f s) = (term9 A B y f s)).
Proof. exact (eq_refl (term7 A B y s f)). Qed.
Lemma lem4606482 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4606483 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem4606484 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem4606483 A s) (@lem4606482 A s)). Qed.
Lemma lem4606485 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem4606484 A s t). Qed.
Lemma lem4606486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term13 A s t).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem4606487 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (EQ_MP (@lem4606486 A s t) (@lem4606485 A s t)). Qed.
Lemma lem4606488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term14 A s t x.
Proof. exact (@lem4606487 A s t x). Qed.
Lemma lem4606489 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A s t x) = ((term15 A x s t) = (term16 A s x t)).
Proof. exact (eq_refl (term14 A s t x)). Qed.
Lemma lem4606515 {_83095 : Type'} : term17 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4606516 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (@lem4606515 _83095 p). Qed.
Lemma lem4606517 {_83095 : Type'} (p : _83095 -> Prop) : (term18 _83095 p) = (term19 _83095 p).
Proof. exact (eq_refl (term18 _83095 p)). Qed.
Lemma lem4606518 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (EQ_MP (@lem4606517 _83095 p) (@lem4606516 _83095 p)). Qed.
Lemma lem4606519 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term20 _83095 p x.
Proof. exact (@lem4606518 _83095 p x). Qed.
Lemma lem4606520 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 p x) = ((term21 _83095 x p) = (p x)).
Proof. exact (eq_refl (term20 _83095 p x)). Qed.
Lemma lem4606552 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term22 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4606553 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term23 _88905 _89106 Q P.
Proof. exact (@lem4606552 _88905 _89106 Q P). Qed.
Lemma lem4606554 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term23 _88905 _89106 Q P) = (term24 _88905 _89106 P Q).
Proof. exact (eq_refl (term23 _88905 _89106 Q P)). Qed.
Lemma lem4606555 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term24 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4606554 _88905 _89106 P Q) (@lem4606553 _88905 _89106 Q P)). Qed.
Lemma lem4606556 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term25 _88905 _89106 P Q f.
Proof. exact (@lem4606555 _88905 _89106 P Q f). Qed.
Lemma lem4606557 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term25 _88905 _89106 P Q f) = ((term26 _88905 _89106 P f Q) = (term27 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term25 _88905 _89106 P Q f)). Qed.
Lemma lem4606559 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term28 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4606560 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term28 _87967 _87968 P f) = (term29 _87967 _87968 P f).
Proof. exact (eq_refl (term28 _87967 _87968 P f)). Qed.
Lemma lem4606561 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term29 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4606560 _87967 _87968 P f) (@lem4606559 _87967 _87968 P f)). Qed.
Lemma lem4606562 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term30 _87967 _87968 P f s.
Proof. exact (@lem4606561 _87967 _87968 P f s). Qed.
Lemma lem4606563 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term30 _87967 _87968 P f s) = ((term31 _87967 _87968 f s P) = (term32 _87967 _87968 s P f)).
Proof. exact (eq_refl (term30 _87967 _87968 P f s)). Qed.
Lemma lem4606565 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4606566 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem4606567 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (EQ_MP (@lem4606566 A s) (@lem4606565 A s)). Qed.
Lemma lem4606568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (@lem4606567 A s t). Qed.
Lemma lem4606569 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = ((@SUBSET A s t) = (term36 A s t)).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem4606571 {_84841 : Type'} (s : _84841 -> Prop) : term37 _84841 s.
Proof. exact (@lem3238518 _84841 s). Qed.
Lemma lem4606572 {_84841 : Type'} (s : _84841 -> Prop) : (term37 _84841 s) = (term38 _84841 s).
Proof. exact (eq_refl (term37 _84841 s)). Qed.
Lemma lem4606573 {_84841 : Type'} (s : _84841 -> Prop) : term38 _84841 s.
Proof. exact (EQ_MP (@lem4606572 _84841 s) (@lem4606571 _84841 s)). Qed.
Lemma lem4606574 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : term39 _84841 s t.
Proof. exact (@lem4606573 _84841 s t). Qed.
Lemma lem4606575 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : (term39 _84841 s t) = (term40 _84841 s t).
Proof. exact (eq_refl (term39 _84841 s t)). Qed.
Lemma lem4606576 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) : term40 _84841 s t.
Proof. exact (EQ_MP (@lem4606575 _84841 s t) (@lem4606574 _84841 s t)). Qed.
Lemma lem4606577 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : term41 _84841 s t u.
Proof. exact (@lem4606576 _84841 s t u). Qed.
Lemma lem4606578 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term41 _84841 s t u) = ((term42 _84841 s t u) = (term43 _84841 s t u)).
Proof. exact (eq_refl (term41 _84841 s t u)). Qed.
Lemma lem4606580 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem4606581 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term45 A s.
Proof. exact (@lem4606580 A h1 s). Qed.
Lemma lem4606582 {A : Type'} (s : A -> Prop) : (term45 A s) = (term46 A s).
Proof. exact (eq_refl (term45 A s)). Qed.
Lemma lem4606583 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term46 A s.
Proof. exact (EQ_MP (@lem4606582 A s) (@lem4606581 A s h1)). Qed.
Lemma lem4606584 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A) : term47 A s t.
Proof. exact (@lem4606583 A s h1 t). Qed.
Lemma lem4606585 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term47 A s t) = (term48 A s t).
Proof. exact (eq_refl (term47 A s t)). Qed.
Lemma lem4606586 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A) : term48 A s t.
Proof. exact (EQ_MP (@lem4606585 A s t) (@lem4606584 A s t h1)). Qed.
Lemma lem4606587 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term49 A t s) : term49 A t s.
Proof. exact (h1). Qed.
Lemma lem4606588 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A) (h2 : term49 A t s) : s = t.
Proof. exact (@lem4606586 A s t h1 (@lem4606587 A t s h2)). Qed.
Lemma lem4606589 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term49 A t s) : term50 A s t.
Proof. exact (fun h0 : term44 A => @lem4606588 A t s h0 h1). Qed.
Lemma lem4606590 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem4606591 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term44 A) (h2 : term49 A t s) : s = t.
Proof. exact (@lem4606589 A t s h2 (@lem4606590 A h1)). Qed.
Lemma lem4606592 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A) : term48 A s t.
Proof. exact (fun h0 : term49 A t s => @lem4606591 A t s h1 h0). Qed.
Lemma lem4606593 {A : Type'} (s : A -> Prop) (h1 : term44 A) : term46 A s.
Proof. exact (fun t : A -> Prop => @lem4606592 A s t h1). Qed.
Lemma lem4606594 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (fun s : A -> Prop => @lem4606593 A s h1). Qed.
Lemma lem4606595 {A : Type'} : term51 A.
Proof. exact (fun h0 : term44 A => @lem4606594 A h0). Qed.
Lemma lem4606596 {A : Type'} : term44 A.
Proof. exact (@lem4606595 A (@lem3218208 A)). Qed.
Lemma lem4606597 {A : Type'} (s : A -> Prop) : term45 A s.
Proof. exact (@lem4606596 A s). Qed.
Lemma lem4606598 {A : Type'} (s : A -> Prop) : (term45 A s) = (term46 A s).
Proof. exact (eq_refl (term45 A s)). Qed.
Lemma lem4606599 {A : Type'} (s : A -> Prop) : term46 A s.
Proof. exact (EQ_MP (@lem4606598 A s) (@lem4606597 A s)). Qed.
Lemma lem4606600 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term47 A s t.
Proof. exact (@lem4606599 A s t). Qed.
Lemma lem4606601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term47 A s t) = (term48 A s t).
Proof. exact (eq_refl (term47 A s t)). Qed.
Lemma lem4606607 {_88341 : Type'} : term52 _88341.
Proof. exact (proj1 (@lem3400385 _88341 Prop)). Qed.
Lemma lem4606608 {_88341 : Type'} (a : _88341) : term53 _88341 a.
Proof. exact (@lem4606607 _88341 a). Qed.
Lemma lem4606609 {_88341 : Type'} (a : _88341) : (term53 _88341 a) = ((term54 _88341 a) = (@INSERT _88341 a (@EMPTY _88341))).
Proof. exact (eq_refl (term53 _88341 a)). Qed.
Lemma lem4606611 {A : Type'} (s : A -> Prop) : term55 A s.
Proof. exact (@lem3220121 A s). Qed.
Lemma lem4606612 {A : Type'} (s : A -> Prop) : (term55 A s) = ((@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem4606614 {A : Type'} (x : A) : term56 A x.
Proof. exact (@lem3311905 A x). Qed.
Lemma lem4606615 {A : Type'} (x : A) : (term56 A x) = (term57 A x).
Proof. exact (eq_refl (term56 A x)). Qed.
Lemma lem4606616 {A : Type'} (x : A) : term57 A x.
Proof. exact (EQ_MP (@lem4606615 A x) (@lem4606614 A x)). Qed.
Lemma lem4606617 {A : Type'} (x : A) (s : A -> Prop) : term58 A x s.
Proof. exact (@lem4606616 A x s). Qed.
Lemma lem4606618 {A : Type'} (s : A -> Prop) (x : A) : (term58 A x s) = (term59 A s x).
Proof. exact (eq_refl (term58 A x s)). Qed.
Lemma lem4606619 {A : Type'} (s : A -> Prop) (x : A) : term59 A s x.
Proof. exact (EQ_MP (@lem4606618 A s x) (@lem4606617 A x s)). Qed.
Lemma lem4606620 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term60 A s x t.
Proof. exact (@lem4606619 A s x t). Qed.
Lemma lem4606621 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term60 A s x t) = ((term61 A s x t) = (term62 A s x t)).
Proof. exact (eq_refl (term60 A s x t)). Qed.
Lemma lem4606632 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4606612 A s) (@lem4606611 A s)). Qed.
Lemma lem4606633 {_108216 : Type'} (s : _108216 -> Prop) : (@SUBSET _108216 s (@EMPTY _108216)) = (s = (@EMPTY _108216)).
Proof. exact (@lem4606632 _108216 s). Qed.
Lemma lem4606636 {_108216 : Type'} (GEN_PVAR_161 : _108216 -> Prop) : (@SETSPEC (_108216 -> Prop) GEN_PVAR_161) = (@SETSPEC (_108216 -> Prop) GEN_PVAR_161).
Proof. exact (eq_refl (@SETSPEC (_108216 -> Prop) GEN_PVAR_161)). Qed.
Lemma lem4606637 {_108216 : Type'} (GEN_PVAR_161 : _108216 -> Prop) (s : _108216 -> Prop) : (term63 _108216 GEN_PVAR_161 s) = (term64 _108216 GEN_PVAR_161 s).
Proof. exact (MK_COMB (@lem4606636 _108216 GEN_PVAR_161) (@lem4606633 _108216 s)). Qed.
Lemma lem4606638 {_108216 : Type'} (s : _108216 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4606639 {_108216 : Type'} (GEN_PVAR_161 : _108216 -> Prop) (s : _108216 -> Prop) : (term65 _108216 GEN_PVAR_161 s) = (term66 _108216 GEN_PVAR_161 s).
Proof. exact (MK_COMB (@lem4606637 _108216 GEN_PVAR_161 s) (@lem4606638 _108216 s)). Qed.
Lemma lem4606640 {_108216 : Type'} (GEN_PVAR_161 : _108216 -> Prop) : (term67 _108216 GEN_PVAR_161) = (term68 _108216 GEN_PVAR_161).
Proof. exact (fun_ext (fun s : _108216 -> Prop => @lem4606639 _108216 GEN_PVAR_161 s)). Qed.
Lemma lem4606641 {_108216 : Type'} : (@ex (_108216 -> Prop)) = (@ex (_108216 -> Prop)).
Proof. exact (eq_refl (@ex (_108216 -> Prop))). Qed.
Lemma lem4606642 {_108216 : Type'} (GEN_PVAR_161 : _108216 -> Prop) : (term69 _108216 GEN_PVAR_161) = (term70 _108216 GEN_PVAR_161).
Proof. exact (MK_COMB (@lem4606641 _108216) (@lem4606640 _108216 GEN_PVAR_161)). Qed.
Lemma lem4606647 {_108216 : Type'} : (term71 _108216) = (term72 _108216).
Proof. exact (fun_ext (fun GEN_PVAR_161 : _108216 -> Prop => @lem4606642 _108216 GEN_PVAR_161)). Qed.
Lemma lem4606648 {_108216 : Type'} : (@GSPEC (_108216 -> Prop)) = (@GSPEC (_108216 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_108216 -> Prop))). Qed.
Lemma lem4606649 {_108216 : Type'} : (term73 _108216) = (term74 _108216).
Proof. exact (MK_COMB (@lem4606648 _108216) (@lem4606647 _108216)). Qed.
Lemma lem4606653 {_88341 : Type'} (a : _88341) : (term54 _88341 a) = (@INSERT _88341 a (@EMPTY _88341)).
Proof. exact (EQ_MP (@lem4606609 _88341 a) (@lem4606608 _88341 a)). Qed.
Lemma lem4606654 {_108216 : Type'} (a : _108216 -> Prop) : (term75 _108216 a) = (@INSERT (_108216 -> Prop) a (@EMPTY (_108216 -> Prop))).
Proof. exact (@lem4606653 (_108216 -> Prop) a). Qed.
Lemma lem4606655 {_108216 : Type'} : (term74 _108216) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))).
Proof. exact (@lem4606654 _108216 (@EMPTY _108216)). Qed.
Lemma lem4606656 {_108216 : Type'} : (term73 _108216) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))).
Proof. exact (TRANS (@lem4606649 _108216) (@lem4606655 _108216)). Qed.
Lemma lem4606657 {_108216 : Type'} : (@eq ((_108216 -> Prop) -> Prop)) = (@eq ((_108216 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_108216 -> Prop) -> Prop))). Qed.
Lemma lem4606658 {_108216 : Type'} : (term76 _108216) = (term77 _108216).
Proof. exact (MK_COMB (@lem4606657 _108216) (@lem4606656 _108216)). Qed.
Lemma lem4606659 {_108216 : Type'} : (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))).
Proof. exact (eq_refl (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))). Qed.
Lemma lem4606660 {_108216 : Type'} : ((term73 _108216) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))) = ((@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))).
Proof. exact (MK_COMB (@lem4606658 _108216) (@lem4606659 _108216)). Qed.
Lemma lem4606662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4606663 {_108216 : Type'} (x : type686 _108216) : (x = x) = True.
Proof. exact (@lem4606662 (type686 _108216) x). Qed.
Lemma lem4606664 {_108216 : Type'} : ((@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop))) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))) = True.
Proof. exact (@lem4606663 _108216 (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))). Qed.
Lemma lem4606665 {_108216 : Type'} : ((term73 _108216) = (@INSERT (_108216 -> Prop) (@EMPTY _108216) (@EMPTY (_108216 -> Prop)))) = True.
Proof. exact (TRANS (@lem4606660 _108216) (@lem4606664 _108216)). Qed.
Lemma lem4606666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606667 {_108216 : Type'} : (term78 _108216) = (and True).
Proof. exact (MK_COMB (@lem4606666) (@lem4606665 _108216)). Qed.
Lemma lem4606683 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term61 A s x t) = (term62 A s x t).
Proof. exact (EQ_MP (@lem4606621 A s x t) (@lem4606620 A s x t)). Qed.
Lemma lem4606684 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term61 A s x t) = (term62 A s x t).
Proof. exact (@lem4606683 A s x t). Qed.
Lemma lem4606685 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term61 A s a t) = (term62 A s a t).
Proof. exact (@lem4606684 A s a t). Qed.
Lemma lem4606686 {A : Type'} (GEN_PVAR_162 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_162) = (@SETSPEC (A -> Prop) GEN_PVAR_162).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_162)). Qed.
Lemma lem4606687 {A : Type'} (GEN_PVAR_162 : A -> Prop) (s : A -> Prop) (a : A) (t : A -> Prop) : (term79 A GEN_PVAR_162 s a t) = (term80 A GEN_PVAR_162 s a t).
Proof. exact (MK_COMB (@lem4606686 A GEN_PVAR_162) (@lem4606685 A s a t)). Qed.
Lemma lem4606688 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4606689 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) (s : A -> Prop) : (term81 A GEN_PVAR_162 a t s) = (term82 A GEN_PVAR_162 a t s).
Proof. exact (MK_COMB (@lem4606687 A GEN_PVAR_162 s a t) (@lem4606688 A s)). Qed.
Lemma lem4606690 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term83 A GEN_PVAR_162 a t) = (term84 A GEN_PVAR_162 a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606689 A GEN_PVAR_162 a t s)). Qed.
Lemma lem4606691 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4606692 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term85 A GEN_PVAR_162 a t) = (term86 A GEN_PVAR_162 a t).
Proof. exact (MK_COMB (@lem4606691 A) (@lem4606690 A GEN_PVAR_162 a t)). Qed.
Lemma lem4606697 {A : Type'} (a : A) (t : A -> Prop) : (term87 A a t) = (term88 A a t).
Proof. exact (fun_ext (fun GEN_PVAR_162 : A -> Prop => @lem4606692 A GEN_PVAR_162 a t)). Qed.
Lemma lem4606698 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4606699 {A : Type'} (a : A) (t : A -> Prop) : (term89 A a t) = (term90 A a t).
Proof. exact (MK_COMB (@lem4606698 A) (@lem4606697 A a t)). Qed.
Lemma lem4606700 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4606701 {A : Type'} (a : A) (t : A -> Prop) : (term91 A a t) = (term92 A a t).
Proof. exact (MK_COMB (@lem4606700 A) (@lem4606699 A a t)). Qed.
Lemma lem4606710 {A : Type'} (a : A) (t : A -> Prop) : (term93 A a t) = (term93 A a t).
Proof. exact (eq_refl (term93 A a t)). Qed.
Lemma lem4606711 {A : Type'} (a : A) (t : A -> Prop) : ((term89 A a t) = (term93 A a t)) = ((term90 A a t) = (term93 A a t)).
Proof. exact (MK_COMB (@lem4606701 A a t) (@lem4606710 A a t)). Qed.
Lemma lem4606714 {A : Type'} (a : A) : (term94 A a) = (term95 A a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4606711 A a t)). Qed.
Lemma lem4606715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606716 {A : Type'} (a : A) : (term96 A a) = (term97 A a).
Proof. exact (MK_COMB (@lem4606715 A) (@lem4606714 A a)). Qed.
Lemma lem4606721 {A : Type'} : (term98 A) = (term99 A).
Proof. exact (fun_ext (fun a : A => @lem4606716 A a)). Qed.
Lemma lem4606722 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4606723 {A : Type'} : (term100 A) = (term101 A).
Proof. exact (MK_COMB (@lem4606722 A) (@lem4606721 A)). Qed.
Lemma lem4606728 {_108216 A : Type'} : (term102 _108216 A) = (term103 A).
Proof. exact (MK_COMB (@lem4606667 _108216) (@lem4606723 A)). Qed.
Lemma lem4606730 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4606731 {A : Type'} : (term103 A) = (term101 A).
Proof. exact (@lem4606730 (term101 A)). Qed.
Lemma lem4606754 {_108216 A : Type'} : (term102 _108216 A) = (term101 A).
Proof. exact (TRANS (@lem4606728 _108216 A) (@lem4606731 A)). Qed.
Lemma lem4606755 {_108216 A : Type'} : (term101 A) = (term102 _108216 A).
Proof. exact (SYM (@lem4606754 _108216 A)). Qed.
Lemma lem4606757 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term48 A s t.
Proof. exact (EQ_MP (@lem4606601 A s t) (@lem4606600 A s t)). Qed.
Lemma lem4606758 {A : Type'} (s : type686 A) (t : type686 A) : term104 A s t.
Proof. exact (@lem4606757 (A -> Prop) s t). Qed.
Lemma lem4606759 {A : Type'} (a : A) (t : A -> Prop) : term105 A a t.
Proof. exact (@lem4606758 A (term90 A a t) (term93 A a t)). Qed.
Lemma lem4606775 {_84841 : Type'} (s : _84841 -> Prop) (t : _84841 -> Prop) (u : _84841 -> Prop) : (term42 _84841 s t u) = (term43 _84841 s t u).
Proof. exact (EQ_MP (@lem4606578 _84841 s t u) (@lem4606577 _84841 s t u)). Qed.
Lemma lem4606776 {A : Type'} (s : type686 A) (t : type686 A) (u : type686 A) : (term106 A s t u) = (term107 A s t u).
Proof. exact (@lem4606775 (A -> Prop) s t u). Qed.
Lemma lem4606777 {A : Type'} (a : A) (t : A -> Prop) : (term108 A a t) = (term109 A a t).
Proof. exact (@lem4606776 A (term110 A t) (term111 A a t) (term90 A a t)). Qed.
Lemma lem4606796 {A : Type'} (a : A) (t : A -> Prop) : (term112 A a t) = (term112 A a t).
Proof. exact (eq_refl (term112 A a t)). Qed.
Lemma lem4606797 {A : Type'} (a : A) (t : A -> Prop) : (term113 A a t) = (term114 A a t).
Proof. exact (MK_COMB (@lem4606796 A a t) (@lem4606777 A a t)). Qed.
Lemma lem4606800 {A : Type'} (a : A) (t : A -> Prop) : (term114 A a t) = (term113 A a t).
Proof. exact (SYM (@lem4606797 A a t)). Qed.
Lemma lem4606804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem4606569 A s t) (@lem4606568 A s t)). Qed.
Lemma lem4606805 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem4606804 (A -> Prop) s t). Qed.
Lemma lem4606806 {A : Type'} (a : A) (t : A -> Prop) : (term116 A a t) = (term117 A a t).
Proof. exact (@lem4606805 A (term90 A a t) (term93 A a t)). Qed.
Lemma lem4606807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606808 {A : Type'} (a : A) (t : A -> Prop) : (term112 A a t) = (term118 A a t).
Proof. exact (MK_COMB (@lem4606807) (@lem4606806 A a t)). Qed.
Lemma lem4606812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem4606569 A s t) (@lem4606568 A s t)). Qed.
Lemma lem4606813 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem4606812 (A -> Prop) s t). Qed.
Lemma lem4606814 {A : Type'} (a : A) (t : A -> Prop) : (term119 A a t) = (term120 A a t).
Proof. exact (@lem4606813 A (term110 A t) (term90 A a t)). Qed.
Lemma lem4606815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606816 {A : Type'} (a : A) (t : A -> Prop) : (term121 A a t) = (term122 A a t).
Proof. exact (MK_COMB (@lem4606815) (@lem4606814 A a t)). Qed.
Lemma lem4606818 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem4606569 A s t) (@lem4606568 A s t)). Qed.
Lemma lem4606819 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term115 A s t).
Proof. exact (@lem4606818 (A -> Prop) s t). Qed.
Lemma lem4606820 {A : Type'} (a : A) (t : A -> Prop) : (term123 A a t) = (term124 A a t).
Proof. exact (@lem4606819 A (term111 A a t) (term90 A a t)). Qed.
Lemma lem4606821 {A : Type'} (a : A) (t : A -> Prop) : (term109 A a t) = (term125 A a t).
Proof. exact (MK_COMB (@lem4606816 A a t) (@lem4606820 A a t)). Qed.
Lemma lem4606822 {A : Type'} (a : A) (t : A -> Prop) : (term114 A a t) = (term126 A a t).
Proof. exact (MK_COMB (@lem4606808 A a t) (@lem4606821 A a t)). Qed.
Lemma lem4606823 {A : Type'} (a : A) (t : A -> Prop) : (term126 A a t) = (term114 A a t).
Proof. exact (SYM (@lem4606822 A a t)). Qed.
Lemma lem4606827 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term26 _88905 _89106 P f Q) = (term27 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4606557 _88905 _89106 P Q f) (@lem4606556 _88905 _89106 P Q f)). Qed.
Lemma lem4606828 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term127 A P f Q) = (term128 A P Q f).
Proof. exact (@lem4606827 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4606829 {A : Type'} (a : A) (t : A -> Prop) : (term129 A a t) = (term130 A a t).
Proof. exact (@lem4606828 A (term131 A a t) (term132 A a t) (term133 A)). Qed.
Lemma lem4606830 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term134 A a t s) = (term62 A s a t).
Proof. exact (eq_refl (term134 A a t s)). Qed.
Lemma lem4606831 {A : Type'} (GEN_PVAR_162 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_162) = (@SETSPEC (A -> Prop) GEN_PVAR_162).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_162)). Qed.
Lemma lem4606832 {A : Type'} (GEN_PVAR_162 : A -> Prop) (s : A -> Prop) (a : A) (t : A -> Prop) : (term135 A GEN_PVAR_162 a t s) = (term80 A GEN_PVAR_162 s a t).
Proof. exact (MK_COMB (@lem4606831 A GEN_PVAR_162) (@lem4606830 A s a t)). Qed.
Lemma lem4606833 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606834 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) (s : A -> Prop) : (term137 A GEN_PVAR_162 a t s) = (term82 A GEN_PVAR_162 a t s).
Proof. exact (MK_COMB (@lem4606832 A GEN_PVAR_162 s a t) (@lem4606833 A s)). Qed.
Lemma lem4606835 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term138 A GEN_PVAR_162 a t) = (term84 A GEN_PVAR_162 a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606834 A GEN_PVAR_162 a t s)). Qed.
Lemma lem4606836 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4606837 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term139 A GEN_PVAR_162 a t) = (term86 A GEN_PVAR_162 a t).
Proof. exact (MK_COMB (@lem4606836 A) (@lem4606835 A GEN_PVAR_162 a t)). Qed.
Lemma lem4606838 {A : Type'} (a : A) (t : A -> Prop) : (term140 A a t) = (term88 A a t).
Proof. exact (fun_ext (fun GEN_PVAR_162 : A -> Prop => @lem4606837 A GEN_PVAR_162 a t)). Qed.
Lemma lem4606839 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4606840 {A : Type'} (a : A) (t : A -> Prop) : (term141 A a t) = (term90 A a t).
Proof. exact (MK_COMB (@lem4606839 A) (@lem4606838 A a t)). Qed.
Lemma lem4606841 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4606842 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term142 A x a t) = (term143 A x a t).
Proof. exact (MK_COMB (@lem4606841 A x) (@lem4606840 A a t)). Qed.
Lemma lem4606843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606844 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term144 A x a t) = (term145 A x a t).
Proof. exact (MK_COMB (@lem4606843) (@lem4606842 A x a t)). Qed.
Lemma lem4606845 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term146 A a t x) = (term147 A x a t).
Proof. exact (eq_refl (term146 A a t x)). Qed.
Lemma lem4606846 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term148 A a t x) = (term149 A x a t).
Proof. exact (MK_COMB (@lem4606844 A x a t) (@lem4606845 A x a t)). Qed.
Lemma lem4606847 {A : Type'} (a : A) (t : A -> Prop) : (term150 A a t) = (term151 A a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4606846 A x a t)). Qed.
Lemma lem4606848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606849 {A : Type'} (a : A) (t : A -> Prop) : (term129 A a t) = (term117 A a t).
Proof. exact (MK_COMB (@lem4606848 A) (@lem4606847 A a t)). Qed.
Lemma lem4606850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4606851 {A : Type'} (a : A) (t : A -> Prop) : (term152 A a t) = (term153 A a t).
Proof. exact (MK_COMB (@lem4606850) (@lem4606849 A a t)). Qed.
Lemma lem4606852 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term134 A a t s) = (term62 A s a t).
Proof. exact (eq_refl (term134 A a t s)). Qed.
Lemma lem4606853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606854 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term154 A a t s) = (term155 A s a t).
Proof. exact (MK_COMB (@lem4606853) (@lem4606852 A s a t)). Qed.
Lemma lem4606855 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term156 A a t s) = (term157 A s a t).
Proof. exact (eq_refl (term156 A a t s)). Qed.
Lemma lem4606856 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term158 A a t s) = (term159 A s a t).
Proof. exact (MK_COMB (@lem4606854 A s a t) (@lem4606855 A s a t)). Qed.
Lemma lem4606857 {A : Type'} (a : A) (t : A -> Prop) : (term160 A a t) = (term161 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606856 A s a t)). Qed.
Lemma lem4606858 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606859 {A : Type'} (a : A) (t : A -> Prop) : (term130 A a t) = (term162 A a t).
Proof. exact (MK_COMB (@lem4606858 A) (@lem4606857 A a t)). Qed.
Lemma lem4606860 {A : Type'} (a : A) (t : A -> Prop) : ((term129 A a t) = (term130 A a t)) = ((term117 A a t) = (term162 A a t)).
Proof. exact (MK_COMB (@lem4606851 A a t) (@lem4606859 A a t)). Qed.
Lemma lem4606861 {A : Type'} (a : A) (t : A -> Prop) : (term117 A a t) = (term162 A a t).
Proof. exact (EQ_MP (@lem4606860 A a t) (@lem4606829 A a t)). Qed.
Lemma lem4606869 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4606870 {A : Type'} (f : type672 A) (y : A -> Prop) : (term164 A f y) = (f y).
Proof. exact (@lem4606869 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4606871 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (@lem4606870 A (term133 A) s). Qed.
Lemma lem4606872 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606873 {A : Type'} : (term166 A) = (term133 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606872 A s)). Qed.
Lemma lem4606874 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4606875 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem4606873 A) (@lem4606874 A s)). Qed.
Lemma lem4606876 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4606877 {A : Type'} (s : A -> Prop) : (term167 A s) = (term168 A s).
Proof. exact (MK_COMB (@lem4606876 A) (@lem4606875 A s)). Qed.
Lemma lem4606878 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606879 {A : Type'} (s : A -> Prop) : ((term165 A s) = (term136 A s)) = ((term136 A s) = s).
Proof. exact (MK_COMB (@lem4606877 A s) (@lem4606878 A s)). Qed.
Lemma lem4606880 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (EQ_MP (@lem4606879 A s) (@lem4606871 A s)). Qed.
Lemma lem4606881 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4606882 {A : Type'} (s : A -> Prop) : (term169 A s) = (@IN (A -> Prop) s).
Proof. exact (MK_COMB (@lem4606881 A) (@lem4606880 A s)). Qed.
Lemma lem4606891 {A : Type'} (a : A) (t : A -> Prop) : (term93 A a t) = (term93 A a t).
Proof. exact (eq_refl (term93 A a t)). Qed.
Lemma lem4606892 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term157 A s a t) = (term147 A s a t).
Proof. exact (MK_COMB (@lem4606882 A s) (@lem4606891 A a t)). Qed.
Lemma lem4606893 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term155 A s a t) = (term155 A s a t).
Proof. exact (eq_refl (term155 A s a t)). Qed.
Lemma lem4606894 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term159 A s a t) = (term170 A s a t).
Proof. exact (MK_COMB (@lem4606893 A s a t) (@lem4606892 A s a t)). Qed.
Lemma lem4606897 {A : Type'} (a : A) (t : A -> Prop) : (term161 A a t) = (term171 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606894 A s a t)). Qed.
Lemma lem4606898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606899 {A : Type'} (a : A) (t : A -> Prop) : (term162 A a t) = (term172 A a t).
Proof. exact (MK_COMB (@lem4606898 A) (@lem4606897 A a t)). Qed.
Lemma lem4606904 {A : Type'} (a : A) (t : A -> Prop) : (term117 A a t) = (term172 A a t).
Proof. exact (TRANS (@lem4606861 A a t) (@lem4606899 A a t)). Qed.
Lemma lem4606905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606906 {A : Type'} (a : A) (t : A -> Prop) : (term118 A a t) = (term173 A a t).
Proof. exact (MK_COMB (@lem4606905) (@lem4606904 A a t)). Qed.
Lemma lem4606910 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term26 _88905 _89106 P f Q) = (term27 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4606557 _88905 _89106 P Q f) (@lem4606556 _88905 _89106 P Q f)). Qed.
Lemma lem4606911 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term127 A P f Q) = (term128 A P Q f).
Proof. exact (@lem4606910 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4606912 {A : Type'} (a : A) (t : A -> Prop) : (term174 A a t) = (term175 A a t).
Proof. exact (@lem4606911 A (term176 A t) (term177 A a t) (term133 A)). Qed.
Lemma lem4606913 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4606914 {A : Type'} (GEN_PVAR_163 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_163) = (@SETSPEC (A -> Prop) GEN_PVAR_163).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_163)). Qed.
Lemma lem4606915 {A : Type'} (GEN_PVAR_163 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term179 A GEN_PVAR_163 t s) = (term180 A GEN_PVAR_163 s t).
Proof. exact (MK_COMB (@lem4606914 A GEN_PVAR_163) (@lem4606913 A s t)). Qed.
Lemma lem4606916 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606917 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term181 A GEN_PVAR_163 t s) = (term182 A GEN_PVAR_163 t s).
Proof. exact (MK_COMB (@lem4606915 A GEN_PVAR_163 s t) (@lem4606916 A s)). Qed.
Lemma lem4606918 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) : (term183 A GEN_PVAR_163 t) = (term184 A GEN_PVAR_163 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606917 A GEN_PVAR_163 t s)). Qed.
Lemma lem4606919 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4606920 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) : (term185 A GEN_PVAR_163 t) = (term186 A GEN_PVAR_163 t).
Proof. exact (MK_COMB (@lem4606919 A) (@lem4606918 A GEN_PVAR_163 t)). Qed.
Lemma lem4606921 {A : Type'} (t : A -> Prop) : (term187 A t) = (term188 A t).
Proof. exact (fun_ext (fun GEN_PVAR_163 : A -> Prop => @lem4606920 A GEN_PVAR_163 t)). Qed.
Lemma lem4606922 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4606923 {A : Type'} (t : A -> Prop) : (term189 A t) = (term110 A t).
Proof. exact (MK_COMB (@lem4606922 A) (@lem4606921 A t)). Qed.
Lemma lem4606924 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4606925 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term190 A x t) = (term191 A x t).
Proof. exact (MK_COMB (@lem4606924 A x) (@lem4606923 A t)). Qed.
Lemma lem4606926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606927 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term192 A x t) = (term193 A x t).
Proof. exact (MK_COMB (@lem4606926) (@lem4606925 A x t)). Qed.
Lemma lem4606928 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term194 A a t x) = (term143 A x a t).
Proof. exact (eq_refl (term194 A a t x)). Qed.
Lemma lem4606929 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term195 A a t x) = (term196 A x a t).
Proof. exact (MK_COMB (@lem4606927 A x t) (@lem4606928 A x a t)). Qed.
Lemma lem4606930 {A : Type'} (a : A) (t : A -> Prop) : (term197 A a t) = (term198 A a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4606929 A x a t)). Qed.
Lemma lem4606931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606932 {A : Type'} (a : A) (t : A -> Prop) : (term174 A a t) = (term120 A a t).
Proof. exact (MK_COMB (@lem4606931 A) (@lem4606930 A a t)). Qed.
Lemma lem4606933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4606934 {A : Type'} (a : A) (t : A -> Prop) : (term199 A a t) = (term200 A a t).
Proof. exact (MK_COMB (@lem4606933) (@lem4606932 A a t)). Qed.
Lemma lem4606935 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4606936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4606937 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term201 A t s) = (term202 A s t).
Proof. exact (MK_COMB (@lem4606936) (@lem4606935 A s t)). Qed.
Lemma lem4606938 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term203 A a t s) = (term204 A s a t).
Proof. exact (eq_refl (term203 A a t s)). Qed.
Lemma lem4606939 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term205 A a t s) = (term206 A s a t).
Proof. exact (MK_COMB (@lem4606937 A s t) (@lem4606938 A s a t)). Qed.
Lemma lem4606940 {A : Type'} (a : A) (t : A -> Prop) : (term207 A a t) = (term208 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606939 A s a t)). Qed.
Lemma lem4606941 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606942 {A : Type'} (a : A) (t : A -> Prop) : (term175 A a t) = (term209 A a t).
Proof. exact (MK_COMB (@lem4606941 A) (@lem4606940 A a t)). Qed.
Lemma lem4606943 {A : Type'} (a : A) (t : A -> Prop) : ((term174 A a t) = (term175 A a t)) = ((term120 A a t) = (term209 A a t)).
Proof. exact (MK_COMB (@lem4606934 A a t) (@lem4606942 A a t)). Qed.
Lemma lem4606944 {A : Type'} (a : A) (t : A -> Prop) : (term120 A a t) = (term209 A a t).
Proof. exact (EQ_MP (@lem4606943 A a t) (@lem4606912 A a t)). Qed.
Lemma lem4606952 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4606953 {A : Type'} (f : type672 A) (y : A -> Prop) : (term164 A f y) = (f y).
Proof. exact (@lem4606952 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4606954 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (@lem4606953 A (term133 A) s). Qed.
Lemma lem4606955 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606956 {A : Type'} : (term166 A) = (term133 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606955 A s)). Qed.
Lemma lem4606957 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4606958 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem4606956 A) (@lem4606957 A s)). Qed.
Lemma lem4606959 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4606960 {A : Type'} (s : A -> Prop) : (term167 A s) = (term168 A s).
Proof. exact (MK_COMB (@lem4606959 A) (@lem4606958 A s)). Qed.
Lemma lem4606961 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4606962 {A : Type'} (s : A -> Prop) : ((term165 A s) = (term136 A s)) = ((term136 A s) = s).
Proof. exact (MK_COMB (@lem4606960 A s) (@lem4606961 A s)). Qed.
Lemma lem4606963 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (EQ_MP (@lem4606962 A s) (@lem4606954 A s)). Qed.
Lemma lem4606964 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4606965 {A : Type'} (s : A -> Prop) : (term169 A s) = (@IN (A -> Prop) s).
Proof. exact (MK_COMB (@lem4606964 A) (@lem4606963 A s)). Qed.
Lemma lem4606970 {A : Type'} (a : A) (t : A -> Prop) : (term90 A a t) = (term90 A a t).
Proof. exact (eq_refl (term90 A a t)). Qed.
Lemma lem4606971 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term204 A s a t) = (term143 A s a t).
Proof. exact (MK_COMB (@lem4606965 A s) (@lem4606970 A a t)). Qed.
Lemma lem4606972 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term202 A s t).
Proof. exact (eq_refl (term202 A s t)). Qed.
Lemma lem4606973 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term206 A s a t) = (term210 A s a t).
Proof. exact (MK_COMB (@lem4606972 A s t) (@lem4606971 A s a t)). Qed.
Lemma lem4606976 {A : Type'} (a : A) (t : A -> Prop) : (term208 A a t) = (term211 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4606973 A s a t)). Qed.
Lemma lem4606977 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606978 {A : Type'} (a : A) (t : A -> Prop) : (term209 A a t) = (term212 A a t).
Proof. exact (MK_COMB (@lem4606977 A) (@lem4606976 A a t)). Qed.
Lemma lem4606983 {A : Type'} (a : A) (t : A -> Prop) : (term120 A a t) = (term212 A a t).
Proof. exact (TRANS (@lem4606944 A a t) (@lem4606978 A a t)). Qed.
Lemma lem4606984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4606985 {A : Type'} (a : A) (t : A -> Prop) : (term122 A a t) = (term213 A a t).
Proof. exact (MK_COMB (@lem4606984) (@lem4606983 A a t)). Qed.
Lemma lem4606987 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term31 _87967 _87968 f s P) = (term32 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4606563 _87967 _87968 s P f) (@lem4606562 _87967 _87968 P f s)). Qed.
Lemma lem4606988 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term214 A f s P) = (term215 A s P f).
Proof. exact (@lem4606987 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4606989 {A : Type'} (t : A -> Prop) (a : A) : (term216 A a t) = (term217 A t a).
Proof. exact (@lem4606988 A (term110 A t) (term177 A a t) (term218 A a)). Qed.
Lemma lem4606990 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term194 A a t x) = (term143 A x a t).
Proof. exact (eq_refl (term194 A a t x)). Qed.
Lemma lem4606991 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term219 A x a t) = (term219 A x a t).
Proof. exact (eq_refl (term219 A x a t)). Qed.
Lemma lem4606992 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term220 A a t x) = (term221 A x a t).
Proof. exact (MK_COMB (@lem4606991 A x a t) (@lem4606990 A x a t)). Qed.
Lemma lem4606993 {A : Type'} (a : A) (t : A -> Prop) : (term222 A a t) = (term223 A a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4606992 A x a t)). Qed.
Lemma lem4606994 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4606995 {A : Type'} (a : A) (t : A -> Prop) : (term216 A a t) = (term124 A a t).
Proof. exact (MK_COMB (@lem4606994 A) (@lem4606993 A a t)). Qed.
Lemma lem4606996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4606997 {A : Type'} (a : A) (t : A -> Prop) : (term224 A a t) = (term225 A a t).
Proof. exact (MK_COMB (@lem4606996) (@lem4606995 A a t)). Qed.
Lemma lem4606998 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term226 A t a x) = (term227 A x a t).
Proof. exact (eq_refl (term226 A t a x)). Qed.
Lemma lem4606999 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term193 A x t) = (term193 A x t).
Proof. exact (eq_refl (term193 A x t)). Qed.
Lemma lem4607000 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term228 A t a x) = (term229 A x a t).
Proof. exact (MK_COMB (@lem4606999 A x t) (@lem4606998 A x a t)). Qed.
Lemma lem4607001 {A : Type'} (a : A) (t : A -> Prop) : (term230 A t a) = (term231 A a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4607000 A x a t)). Qed.
Lemma lem4607002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607003 {A : Type'} (a : A) (t : A -> Prop) : (term217 A t a) = (term232 A a t).
Proof. exact (MK_COMB (@lem4607002 A) (@lem4607001 A a t)). Qed.
Lemma lem4607004 {A : Type'} (a : A) (t : A -> Prop) : ((term216 A a t) = (term217 A t a)) = ((term124 A a t) = (term232 A a t)).
Proof. exact (MK_COMB (@lem4606997 A a t) (@lem4607003 A a t)). Qed.
Lemma lem4607005 {A : Type'} (a : A) (t : A -> Prop) : (term124 A a t) = (term232 A a t).
Proof. exact (EQ_MP (@lem4607004 A a t) (@lem4606989 A t a)). Qed.
Lemma lem4607007 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term26 _88905 _89106 P f Q) = (term27 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4606557 _88905 _89106 P Q f) (@lem4606556 _88905 _89106 P Q f)). Qed.
Lemma lem4607008 {A : Type'} (P : type686 A) (Q : type686 A) (f : type672 A) : (term127 A P f Q) = (term128 A P Q f).
Proof. exact (@lem4607007 (A -> Prop) (A -> Prop) P Q f). Qed.
Lemma lem4607009 {A : Type'} (a : A) (t : A -> Prop) : (term233 A a t) = (term234 A a t).
Proof. exact (@lem4607008 A (term176 A t) (term235 A a t) (term133 A)). Qed.
Lemma lem4607010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4607011 {A : Type'} (GEN_PVAR_164 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_164) = (@SETSPEC (A -> Prop) GEN_PVAR_164).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_164)). Qed.
Lemma lem4607012 {A : Type'} (GEN_PVAR_164 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term179 A GEN_PVAR_164 t s) = (term180 A GEN_PVAR_164 s t).
Proof. exact (MK_COMB (@lem4607011 A GEN_PVAR_164) (@lem4607010 A s t)). Qed.
Lemma lem4607013 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4607014 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term181 A GEN_PVAR_164 t s) = (term182 A GEN_PVAR_164 t s).
Proof. exact (MK_COMB (@lem4607012 A GEN_PVAR_164 s t) (@lem4607013 A s)). Qed.
Lemma lem4607015 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) : (term183 A GEN_PVAR_164 t) = (term184 A GEN_PVAR_164 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607014 A GEN_PVAR_164 t s)). Qed.
Lemma lem4607016 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607017 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) : (term185 A GEN_PVAR_164 t) = (term186 A GEN_PVAR_164 t).
Proof. exact (MK_COMB (@lem4607016 A) (@lem4607015 A GEN_PVAR_164 t)). Qed.
Lemma lem4607018 {A : Type'} (t : A -> Prop) : (term187 A t) = (term188 A t).
Proof. exact (fun_ext (fun GEN_PVAR_164 : A -> Prop => @lem4607017 A GEN_PVAR_164 t)). Qed.
Lemma lem4607019 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4607020 {A : Type'} (t : A -> Prop) : (term189 A t) = (term110 A t).
Proof. exact (MK_COMB (@lem4607019 A) (@lem4607018 A t)). Qed.
Lemma lem4607021 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4607022 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term190 A x t) = (term191 A x t).
Proof. exact (MK_COMB (@lem4607021 A x) (@lem4607020 A t)). Qed.
Lemma lem4607023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607024 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term192 A x t) = (term193 A x t).
Proof. exact (MK_COMB (@lem4607023) (@lem4607022 A x t)). Qed.
Lemma lem4607025 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term236 A a t x) = (term227 A x a t).
Proof. exact (eq_refl (term236 A a t x)). Qed.
Lemma lem4607026 {A : Type'} (x : A -> Prop) (a : A) (t : A -> Prop) : (term237 A a t x) = (term229 A x a t).
Proof. exact (MK_COMB (@lem4607024 A x t) (@lem4607025 A x a t)). Qed.
Lemma lem4607027 {A : Type'} (a : A) (t : A -> Prop) : (term238 A a t) = (term231 A a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4607026 A x a t)). Qed.
Lemma lem4607028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607029 {A : Type'} (a : A) (t : A -> Prop) : (term233 A a t) = (term232 A a t).
Proof. exact (MK_COMB (@lem4607028 A) (@lem4607027 A a t)). Qed.
Lemma lem4607030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607031 {A : Type'} (a : A) (t : A -> Prop) : (term239 A a t) = (term240 A a t).
Proof. exact (MK_COMB (@lem4607030) (@lem4607029 A a t)). Qed.
Lemma lem4607032 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4607033 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607034 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term201 A t s) = (term202 A s t).
Proof. exact (MK_COMB (@lem4607033) (@lem4607032 A s t)). Qed.
Lemma lem4607035 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term241 A a t s) = (term242 A s a t).
Proof. exact (eq_refl (term241 A a t s)). Qed.
Lemma lem4607036 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term243 A a t s) = (term244 A s a t).
Proof. exact (MK_COMB (@lem4607034 A s t) (@lem4607035 A s a t)). Qed.
Lemma lem4607037 {A : Type'} (a : A) (t : A -> Prop) : (term245 A a t) = (term246 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607036 A s a t)). Qed.
Lemma lem4607038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607039 {A : Type'} (a : A) (t : A -> Prop) : (term234 A a t) = (term247 A a t).
Proof. exact (MK_COMB (@lem4607038 A) (@lem4607037 A a t)). Qed.
Lemma lem4607040 {A : Type'} (a : A) (t : A -> Prop) : ((term233 A a t) = (term234 A a t)) = ((term232 A a t) = (term247 A a t)).
Proof. exact (MK_COMB (@lem4607031 A a t) (@lem4607039 A a t)). Qed.
Lemma lem4607041 {A : Type'} (a : A) (t : A -> Prop) : (term232 A a t) = (term247 A a t).
Proof. exact (EQ_MP (@lem4607040 A a t) (@lem4607009 A a t)). Qed.
Lemma lem4607046 {A : Type'} (a : A) (t : A -> Prop) : (term124 A a t) = (term247 A a t).
Proof. exact (TRANS (@lem4607005 A a t) (@lem4607041 A a t)). Qed.
Lemma lem4607050 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4607051 {A : Type'} (f : type672 A) (y : A -> Prop) : (term164 A f y) = (f y).
Proof. exact (@lem4607050 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4607052 {A : Type'} (a : A) (s : A -> Prop) : (term248 A a s) = (term249 A a s).
Proof. exact (@lem4607051 A (term218 A a) (term136 A s)). Qed.
Lemma lem4607053 {A : Type'} (a : A) (s : A -> Prop) : (term250 A a s) = (@INSERT A a s).
Proof. exact (eq_refl (term250 A a s)). Qed.
Lemma lem4607054 {A : Type'} (a : A) : (term251 A a) = (term218 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607053 A a s)). Qed.
Lemma lem4607055 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4607056 {A : Type'} (a : A) (s : A -> Prop) : (term248 A a s) = (term249 A a s).
Proof. exact (MK_COMB (@lem4607054 A a) (@lem4607055 A s)). Qed.
Lemma lem4607057 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4607058 {A : Type'} (a : A) (s : A -> Prop) : (term252 A a s) = (term253 A a s).
Proof. exact (MK_COMB (@lem4607057 A) (@lem4607056 A a s)). Qed.
Lemma lem4607059 {A : Type'} (a : A) (s : A -> Prop) : (term249 A a s) = (term254 A a s).
Proof. exact (eq_refl (term249 A a s)). Qed.
Lemma lem4607060 {A : Type'} (a : A) (s : A -> Prop) : ((term248 A a s) = (term249 A a s)) = ((term249 A a s) = (term254 A a s)).
Proof. exact (MK_COMB (@lem4607058 A a s) (@lem4607059 A a s)). Qed.
Lemma lem4607061 {A : Type'} (a : A) (s : A -> Prop) : (term249 A a s) = (term254 A a s).
Proof. exact (EQ_MP (@lem4607060 A a s) (@lem4607052 A a s)). Qed.
Lemma lem4607063 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4607064 {A : Type'} (f : type672 A) (y : A -> Prop) : (term164 A f y) = (f y).
Proof. exact (@lem4607063 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4607065 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (@lem4607064 A (term133 A) s). Qed.
Lemma lem4607066 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4607067 {A : Type'} : (term166 A) = (term133 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607066 A s)). Qed.
Lemma lem4607068 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4607069 {A : Type'} (s : A -> Prop) : (term165 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem4607067 A) (@lem4607068 A s)). Qed.
Lemma lem4607070 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4607071 {A : Type'} (s : A -> Prop) : (term167 A s) = (term168 A s).
Proof. exact (MK_COMB (@lem4607070 A) (@lem4607069 A s)). Qed.
Lemma lem4607072 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem4607073 {A : Type'} (s : A -> Prop) : ((term165 A s) = (term136 A s)) = ((term136 A s) = s).
Proof. exact (MK_COMB (@lem4607071 A s) (@lem4607072 A s)). Qed.
Lemma lem4607074 {A : Type'} (s : A -> Prop) : (term136 A s) = s.
Proof. exact (EQ_MP (@lem4607073 A s) (@lem4607065 A s)). Qed.
Lemma lem4607075 {A : Type'} (a : A) : (@INSERT A a) = (@INSERT A a).
Proof. exact (eq_refl (@INSERT A a)). Qed.
Lemma lem4607076 {A : Type'} (a : A) (s : A -> Prop) : (term254 A a s) = (@INSERT A a s).
Proof. exact (MK_COMB (@lem4607075 A a) (@lem4607074 A s)). Qed.
Lemma lem4607077 {A : Type'} (a : A) (s : A -> Prop) : (term249 A a s) = (@INSERT A a s).
Proof. exact (TRANS (@lem4607061 A a s) (@lem4607076 A a s)). Qed.
Lemma lem4607078 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem4607079 {A : Type'} (a : A) (s : A -> Prop) : (term255 A a s) = (term256 A a s).
Proof. exact (MK_COMB (@lem4607078 A) (@lem4607077 A a s)). Qed.
Lemma lem4607084 {A : Type'} (a : A) (t : A -> Prop) : (term90 A a t) = (term90 A a t).
Proof. exact (eq_refl (term90 A a t)). Qed.
Lemma lem4607085 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term242 A s a t) = (term257 A s a t).
Proof. exact (MK_COMB (@lem4607079 A a s) (@lem4607084 A a t)). Qed.
Lemma lem4607086 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term202 A s t).
Proof. exact (eq_refl (term202 A s t)). Qed.
Lemma lem4607087 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term244 A s a t) = (term258 A s a t).
Proof. exact (MK_COMB (@lem4607086 A s t) (@lem4607085 A s a t)). Qed.
Lemma lem4607090 {A : Type'} (a : A) (t : A -> Prop) : (term246 A a t) = (term259 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607087 A s a t)). Qed.
Lemma lem4607091 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607092 {A : Type'} (a : A) (t : A -> Prop) : (term247 A a t) = (term260 A a t).
Proof. exact (MK_COMB (@lem4607091 A) (@lem4607090 A a t)). Qed.
Lemma lem4607097 {A : Type'} (a : A) (t : A -> Prop) : (term124 A a t) = (term260 A a t).
Proof. exact (TRANS (@lem4607046 A a t) (@lem4607092 A a t)). Qed.
Lemma lem4607098 {A : Type'} (a : A) (t : A -> Prop) : (term125 A a t) = (term261 A a t).
Proof. exact (MK_COMB (@lem4606985 A a t) (@lem4607097 A a t)). Qed.
Lemma lem4607101 {A : Type'} (a : A) (t : A -> Prop) : (term126 A a t) = (term262 A a t).
Proof. exact (MK_COMB (@lem4606906 A a t) (@lem4607098 A a t)). Qed.
Lemma lem4607104 {A : Type'} (a : A) (t : A -> Prop) : (term262 A a t) = (term126 A a t).
Proof. exact (SYM (@lem4607101 A a t)). Qed.
Lemma lem4607114 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem4606489 A s x t) (@lem4606488 A s t x)). Qed.
Lemma lem4607115 {A : Type'} (s : type686 A) (x : A -> Prop) (t : type686 A) : (term263 A x s t) = (term264 A s x t).
Proof. exact (@lem4607114 (A -> Prop) s x t). Qed.
Lemma lem4607116 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term147 A s a t) = (term265 A s a t).
Proof. exact (@lem4607115 A (term110 A t) s (term111 A a t)). Qed.
Lemma lem4607120 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4606520 _83095 p x) (@lem4606519 _83095 p x)). Qed.
Lemma lem4607121 {A : Type'} (p : type686 A) (x : A -> Prop) : (term266 A x p) = (p x).
Proof. exact (@lem4607120 (A -> Prop) p x). Qed.
Lemma lem4607122 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term267 A s t) = (term178 A t s).
Proof. exact (@lem4607121 A (term176 A t) s). Qed.
Lemma lem4607123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4607124 {A : Type'} (GEN_PVAR_163 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_163) = (@SETSPEC (A -> Prop) GEN_PVAR_163).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_163)). Qed.
Lemma lem4607125 {A : Type'} (GEN_PVAR_163 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term179 A GEN_PVAR_163 t s) = (term180 A GEN_PVAR_163 s t).
Proof. exact (MK_COMB (@lem4607124 A GEN_PVAR_163) (@lem4607123 A s t)). Qed.
Lemma lem4607126 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4607127 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term268 A GEN_PVAR_163 t s) = (term182 A GEN_PVAR_163 t s).
Proof. exact (MK_COMB (@lem4607125 A GEN_PVAR_163 s t) (@lem4607126 A s)). Qed.
Lemma lem4607128 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) : (term269 A GEN_PVAR_163 t) = (term184 A GEN_PVAR_163 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607127 A GEN_PVAR_163 t s)). Qed.
Lemma lem4607129 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607130 {A : Type'} (GEN_PVAR_163 : A -> Prop) (t : A -> Prop) : (term270 A GEN_PVAR_163 t) = (term186 A GEN_PVAR_163 t).
Proof. exact (MK_COMB (@lem4607129 A) (@lem4607128 A GEN_PVAR_163 t)). Qed.
Lemma lem4607131 {A : Type'} (t : A -> Prop) : (term271 A t) = (term188 A t).
Proof. exact (fun_ext (fun GEN_PVAR_163 : A -> Prop => @lem4607130 A GEN_PVAR_163 t)). Qed.
Lemma lem4607132 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4607133 {A : Type'} (t : A -> Prop) : (term272 A t) = (term110 A t).
Proof. exact (MK_COMB (@lem4607132 A) (@lem4607131 A t)). Qed.
Lemma lem4607134 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem4607135 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term267 A s t) = (term191 A s t).
Proof. exact (MK_COMB (@lem4607134 A s) (@lem4607133 A t)). Qed.
Lemma lem4607136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term273 A s t) = (term274 A s t).
Proof. exact (MK_COMB (@lem4607136) (@lem4607135 A s t)). Qed.
Lemma lem4607138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4607139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term267 A s t) = (term178 A t s)) = ((term191 A s t) = (@SUBSET A s t)).
Proof. exact (MK_COMB (@lem4607137 A s t) (@lem4607138 A s t)). Qed.
Lemma lem4607140 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term191 A s t) = (@SUBSET A s t).
Proof. exact (EQ_MP (@lem4607139 A s t) (@lem4607122 A t s)). Qed.
Lemma lem4607141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4607142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term276 A s t).
Proof. exact (MK_COMB (@lem4607141) (@lem4607140 A s t)). Qed.
Lemma lem4607144 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term8 A B y f s) = (term9 A B y f s).
Proof. exact (EQ_MP (@lem4606480 A B y f s) (@lem4606479 A B y s f)). Qed.
Lemma lem4607145 {A : Type'} (y : A -> Prop) (f : type672 A) (s : type686 A) : (term277 A y f s) = (term278 A y f s).
Proof. exact (@lem4607144 (A -> Prop) (A -> Prop) y f s). Qed.
Lemma lem4607146 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term279 A s a t) = (term280 A s a t).
Proof. exact (@lem4607145 A s (term218 A a) (term110 A t)). Qed.
Lemma lem4607156 {A B : Type'} (f : A -> B) (y : A) : (term163 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4607157 {A : Type'} (f : type672 A) (y : A -> Prop) : (term164 A f y) = (f y).
Proof. exact (@lem4607156 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4607158 {A : Type'} (a : A) (x : A -> Prop) : (term281 A a x) = (term250 A a x).
Proof. exact (@lem4607157 A (term218 A a) x). Qed.
Lemma lem4607159 {A : Type'} (a : A) (s : A -> Prop) : (term250 A a s) = (@INSERT A a s).
Proof. exact (eq_refl (term250 A a s)). Qed.
Lemma lem4607160 {A : Type'} (a : A) : (term251 A a) = (term218 A a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607159 A a s)). Qed.
Lemma lem4607161 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4607162 {A : Type'} (a : A) (x : A -> Prop) : (term281 A a x) = (term250 A a x).
Proof. exact (MK_COMB (@lem4607160 A a) (@lem4607161 A x)). Qed.
Lemma lem4607163 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4607164 {A : Type'} (a : A) (x : A -> Prop) : (term282 A a x) = (term283 A a x).
Proof. exact (MK_COMB (@lem4607163 A) (@lem4607162 A a x)). Qed.
Lemma lem4607165 {A : Type'} (a : A) (x : A -> Prop) : (term250 A a x) = (@INSERT A a x).
Proof. exact (eq_refl (term250 A a x)). Qed.
Lemma lem4607166 {A : Type'} (a : A) (x : A -> Prop) : ((term281 A a x) = (term250 A a x)) = ((term250 A a x) = (@INSERT A a x)).
Proof. exact (MK_COMB (@lem4607164 A a x) (@lem4607165 A a x)). Qed.
Lemma lem4607167 {A : Type'} (a : A) (x : A -> Prop) : (term250 A a x) = (@INSERT A a x).
Proof. exact (EQ_MP (@lem4607166 A a x) (@lem4607158 A a x)). Qed.
Lemma lem4607168 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem4607169 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (s = (term250 A a x)) = (s = (@INSERT A a x)).
Proof. exact (MK_COMB (@lem4607168 A s) (@lem4607167 A a x)). Qed.
Lemma lem4607172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607173 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term284 A s a x) = (term285 A s a x).
Proof. exact (MK_COMB (@lem4607172) (@lem4607169 A s a x)). Qed.
Lemma lem4607175 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4606520 _83095 p x) (@lem4606519 _83095 p x)). Qed.
Lemma lem4607176 {A : Type'} (p : type686 A) (x : A -> Prop) : (term266 A x p) = (p x).
Proof. exact (@lem4607175 (A -> Prop) p x). Qed.
Lemma lem4607177 {A : Type'} (t : A -> Prop) (x : A -> Prop) : (term267 A x t) = (term178 A t x).
Proof. exact (@lem4607176 A (term176 A t) x). Qed.
Lemma lem4607178 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A t s) = (@SUBSET A s t).
Proof. exact (eq_refl (term178 A t s)). Qed.
Lemma lem4607179 {A : Type'} (GEN_PVAR_164 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_164) = (@SETSPEC (A -> Prop) GEN_PVAR_164).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_164)). Qed.
Lemma lem4607180 {A : Type'} (GEN_PVAR_164 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term179 A GEN_PVAR_164 t s) = (term180 A GEN_PVAR_164 s t).
Proof. exact (MK_COMB (@lem4607179 A GEN_PVAR_164) (@lem4607178 A s t)). Qed.
Lemma lem4607181 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4607182 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term268 A GEN_PVAR_164 t s) = (term182 A GEN_PVAR_164 t s).
Proof. exact (MK_COMB (@lem4607180 A GEN_PVAR_164 s t) (@lem4607181 A s)). Qed.
Lemma lem4607183 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) : (term269 A GEN_PVAR_164 t) = (term184 A GEN_PVAR_164 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607182 A GEN_PVAR_164 t s)). Qed.
Lemma lem4607184 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607185 {A : Type'} (GEN_PVAR_164 : A -> Prop) (t : A -> Prop) : (term270 A GEN_PVAR_164 t) = (term186 A GEN_PVAR_164 t).
Proof. exact (MK_COMB (@lem4607184 A) (@lem4607183 A GEN_PVAR_164 t)). Qed.
Lemma lem4607186 {A : Type'} (t : A -> Prop) : (term271 A t) = (term188 A t).
Proof. exact (fun_ext (fun GEN_PVAR_164 : A -> Prop => @lem4607185 A GEN_PVAR_164 t)). Qed.
Lemma lem4607187 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4607188 {A : Type'} (t : A -> Prop) : (term272 A t) = (term110 A t).
Proof. exact (MK_COMB (@lem4607187 A) (@lem4607186 A t)). Qed.
Lemma lem4607189 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem4607190 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term267 A x t) = (term191 A x t).
Proof. exact (MK_COMB (@lem4607189 A x) (@lem4607188 A t)). Qed.
Lemma lem4607191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607192 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term273 A x t) = (term274 A x t).
Proof. exact (MK_COMB (@lem4607191) (@lem4607190 A x t)). Qed.
Lemma lem4607193 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term178 A t x) = (@SUBSET A x t).
Proof. exact (eq_refl (term178 A t x)). Qed.
Lemma lem4607194 {A : Type'} (x : A -> Prop) (t : A -> Prop) : ((term267 A x t) = (term178 A t x)) = ((term191 A x t) = (@SUBSET A x t)).
Proof. exact (MK_COMB (@lem4607192 A x t) (@lem4607193 A x t)). Qed.
Lemma lem4607195 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term191 A x t) = (@SUBSET A x t).
Proof. exact (EQ_MP (@lem4607194 A x t) (@lem4607177 A t x)). Qed.
Lemma lem4607196 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term286 A s a x t) = (term287 A s a x t).
Proof. exact (MK_COMB (@lem4607173 A s a x) (@lem4607195 A x t)). Qed.
Lemma lem4607199 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term288 A s a t) = (term289 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4607196 A s a x t)). Qed.
Lemma lem4607200 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607201 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term280 A s a t) = (term290 A s a t).
Proof. exact (MK_COMB (@lem4607200 A) (@lem4607199 A s a t)). Qed.
Lemma lem4607206 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term279 A s a t) = (term290 A s a t).
Proof. exact (TRANS (@lem4607146 A s a t) (@lem4607201 A s a t)). Qed.
Lemma lem4607207 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term265 A s a t) = (term291 A s a t).
Proof. exact (MK_COMB (@lem4607142 A s t) (@lem4607206 A s a t)). Qed.
Lemma lem4607210 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term147 A s a t) = (term291 A s a t).
Proof. exact (TRANS (@lem4607116 A s a t) (@lem4607207 A s a t)). Qed.
Lemma lem4607211 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term155 A s a t) = (term155 A s a t).
Proof. exact (eq_refl (term155 A s a t)). Qed.
Lemma lem4607212 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term170 A s a t) = (term292 A s a t).
Proof. exact (MK_COMB (@lem4607211 A s a t) (@lem4607210 A s a t)). Qed.
Lemma lem4607215 {A : Type'} (a : A) (t : A -> Prop) : (term171 A a t) = (term293 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607212 A s a t)). Qed.
Lemma lem4607216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607217 {A : Type'} (a : A) (t : A -> Prop) : (term172 A a t) = (term294 A a t).
Proof. exact (MK_COMB (@lem4607216 A) (@lem4607215 A a t)). Qed.
Lemma lem4607222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607223 {A : Type'} (a : A) (t : A -> Prop) : (term173 A a t) = (term295 A a t).
Proof. exact (MK_COMB (@lem4607222) (@lem4607217 A a t)). Qed.
Lemma lem4607233 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4606520 _83095 p x) (@lem4606519 _83095 p x)). Qed.
Lemma lem4607234 {A : Type'} (p : type686 A) (x : A -> Prop) : (term266 A x p) = (p x).
Proof. exact (@lem4607233 (A -> Prop) p x). Qed.
Lemma lem4607235 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) : (term296 A s a t) = (term134 A a t s).
Proof. exact (@lem4607234 A (term131 A a t) s). Qed.
Lemma lem4607236 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term134 A a t s) = (term62 A s a t).
Proof. exact (eq_refl (term134 A a t s)). Qed.
Lemma lem4607237 {A : Type'} (GEN_PVAR_162 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_162) = (@SETSPEC (A -> Prop) GEN_PVAR_162).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_162)). Qed.
Lemma lem4607238 {A : Type'} (GEN_PVAR_162 : A -> Prop) (s : A -> Prop) (a : A) (t : A -> Prop) : (term135 A GEN_PVAR_162 a t s) = (term80 A GEN_PVAR_162 s a t).
Proof. exact (MK_COMB (@lem4607237 A GEN_PVAR_162) (@lem4607236 A s a t)). Qed.
Lemma lem4607239 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4607240 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) (s : A -> Prop) : (term297 A GEN_PVAR_162 a t s) = (term82 A GEN_PVAR_162 a t s).
Proof. exact (MK_COMB (@lem4607238 A GEN_PVAR_162 s a t) (@lem4607239 A s)). Qed.
Lemma lem4607241 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term298 A GEN_PVAR_162 a t) = (term84 A GEN_PVAR_162 a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607240 A GEN_PVAR_162 a t s)). Qed.
Lemma lem4607242 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607243 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term299 A GEN_PVAR_162 a t) = (term86 A GEN_PVAR_162 a t).
Proof. exact (MK_COMB (@lem4607242 A) (@lem4607241 A GEN_PVAR_162 a t)). Qed.
Lemma lem4607244 {A : Type'} (a : A) (t : A -> Prop) : (term300 A a t) = (term88 A a t).
Proof. exact (fun_ext (fun GEN_PVAR_162 : A -> Prop => @lem4607243 A GEN_PVAR_162 a t)). Qed.
Lemma lem4607245 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4607246 {A : Type'} (a : A) (t : A -> Prop) : (term301 A a t) = (term90 A a t).
Proof. exact (MK_COMB (@lem4607245 A) (@lem4607244 A a t)). Qed.
Lemma lem4607247 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem4607248 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term296 A s a t) = (term143 A s a t).
Proof. exact (MK_COMB (@lem4607247 A s) (@lem4607246 A a t)). Qed.
Lemma lem4607249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607250 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term302 A s a t) = (term303 A s a t).
Proof. exact (MK_COMB (@lem4607249) (@lem4607248 A s a t)). Qed.
Lemma lem4607251 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term134 A a t s) = (term62 A s a t).
Proof. exact (eq_refl (term134 A a t s)). Qed.
Lemma lem4607252 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term296 A s a t) = (term134 A a t s)) = ((term143 A s a t) = (term62 A s a t)).
Proof. exact (MK_COMB (@lem4607250 A s a t) (@lem4607251 A s a t)). Qed.
Lemma lem4607253 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term143 A s a t) = (term62 A s a t).
Proof. exact (EQ_MP (@lem4607252 A s a t) (@lem4607235 A a t s)). Qed.
Lemma lem4607254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term202 A s t).
Proof. exact (eq_refl (term202 A s t)). Qed.
Lemma lem4607255 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term210 A s a t) = (term304 A s a t).
Proof. exact (MK_COMB (@lem4607254 A s t) (@lem4607253 A s a t)). Qed.
Lemma lem4607258 {A : Type'} (a : A) (t : A -> Prop) : (term211 A a t) = (term305 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607255 A s a t)). Qed.
Lemma lem4607259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607260 {A : Type'} (a : A) (t : A -> Prop) : (term212 A a t) = (term306 A a t).
Proof. exact (MK_COMB (@lem4607259 A) (@lem4607258 A a t)). Qed.
Lemma lem4607265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607266 {A : Type'} (a : A) (t : A -> Prop) : (term213 A a t) = (term307 A a t).
Proof. exact (MK_COMB (@lem4607265) (@lem4607260 A a t)). Qed.
Lemma lem4607274 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4606520 _83095 p x) (@lem4606519 _83095 p x)). Qed.
Lemma lem4607275 {A : Type'} (p : type686 A) (x : A -> Prop) : (term266 A x p) = (p x).
Proof. exact (@lem4607274 (A -> Prop) p x). Qed.
Lemma lem4607276 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term308 A s a t) = (term309 A t a s).
Proof. exact (@lem4607275 A (term131 A a t) (@INSERT A a s)). Qed.
Lemma lem4607277 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term134 A a t s) = (term62 A s a t).
Proof. exact (eq_refl (term134 A a t s)). Qed.
Lemma lem4607278 {A : Type'} (GEN_PVAR_162 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_162) = (@SETSPEC (A -> Prop) GEN_PVAR_162).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_162)). Qed.
Lemma lem4607279 {A : Type'} (GEN_PVAR_162 : A -> Prop) (s : A -> Prop) (a : A) (t : A -> Prop) : (term135 A GEN_PVAR_162 a t s) = (term80 A GEN_PVAR_162 s a t).
Proof. exact (MK_COMB (@lem4607278 A GEN_PVAR_162) (@lem4607277 A s a t)). Qed.
Lemma lem4607280 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4607281 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) (s : A -> Prop) : (term297 A GEN_PVAR_162 a t s) = (term82 A GEN_PVAR_162 a t s).
Proof. exact (MK_COMB (@lem4607279 A GEN_PVAR_162 s a t) (@lem4607280 A s)). Qed.
Lemma lem4607282 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term298 A GEN_PVAR_162 a t) = (term84 A GEN_PVAR_162 a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607281 A GEN_PVAR_162 a t s)). Qed.
Lemma lem4607283 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4607284 {A : Type'} (GEN_PVAR_162 : A -> Prop) (a : A) (t : A -> Prop) : (term299 A GEN_PVAR_162 a t) = (term86 A GEN_PVAR_162 a t).
Proof. exact (MK_COMB (@lem4607283 A) (@lem4607282 A GEN_PVAR_162 a t)). Qed.
Lemma lem4607285 {A : Type'} (a : A) (t : A -> Prop) : (term300 A a t) = (term88 A a t).
Proof. exact (fun_ext (fun GEN_PVAR_162 : A -> Prop => @lem4607284 A GEN_PVAR_162 a t)). Qed.
Lemma lem4607286 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4607287 {A : Type'} (a : A) (t : A -> Prop) : (term301 A a t) = (term90 A a t).
Proof. exact (MK_COMB (@lem4607286 A) (@lem4607285 A a t)). Qed.
Lemma lem4607288 {A : Type'} (a : A) (s : A -> Prop) : (term256 A a s) = (term256 A a s).
Proof. exact (eq_refl (term256 A a s)). Qed.
Lemma lem4607289 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term308 A s a t) = (term257 A s a t).
Proof. exact (MK_COMB (@lem4607288 A a s) (@lem4607287 A a t)). Qed.
Lemma lem4607290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607291 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term310 A s a t) = (term311 A s a t).
Proof. exact (MK_COMB (@lem4607290) (@lem4607289 A s a t)). Qed.
Lemma lem4607292 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term309 A t a s) = (term312 A s a t).
Proof. exact (eq_refl (term309 A t a s)). Qed.
Lemma lem4607293 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term308 A s a t) = (term309 A t a s)) = ((term257 A s a t) = (term312 A s a t)).
Proof. exact (MK_COMB (@lem4607291 A s a t) (@lem4607292 A s a t)). Qed.
Lemma lem4607294 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term257 A s a t) = (term312 A s a t).
Proof. exact (EQ_MP (@lem4607293 A s a t) (@lem4607276 A t a s)). Qed.
Lemma lem4607295 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term202 A s t).
Proof. exact (eq_refl (term202 A s t)). Qed.
Lemma lem4607296 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term258 A s a t) = (term313 A s a t).
Proof. exact (MK_COMB (@lem4607295 A s t) (@lem4607294 A s a t)). Qed.
Lemma lem4607299 {A : Type'} (a : A) (t : A -> Prop) : (term259 A a t) = (term314 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607296 A s a t)). Qed.
Lemma lem4607300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607301 {A : Type'} (a : A) (t : A -> Prop) : (term260 A a t) = (term315 A a t).
Proof. exact (MK_COMB (@lem4607300 A) (@lem4607299 A a t)). Qed.
Lemma lem4607306 {A : Type'} (a : A) (t : A -> Prop) : (term261 A a t) = (term316 A a t).
Proof. exact (MK_COMB (@lem4607266 A a t) (@lem4607301 A a t)). Qed.
Lemma lem4607309 {A : Type'} (a : A) (t : A -> Prop) : (term262 A a t) = (term317 A a t).
Proof. exact (MK_COMB (@lem4607223 A a t) (@lem4607306 A a t)). Qed.
Lemma lem4607312 {A : Type'} (a : A) (t : A -> Prop) : (term317 A a t) = (term262 A a t).
Proof. exact (SYM (@lem4607309 A a t)). Qed.
Lemma lem4607322 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4607323 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4607322 A s t). Qed.
Lemma lem4607330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term318 A s t).
Proof. exact (MK_COMB (@lem4607330) (@lem4607323 A s t)). Qed.
Lemma lem4607333 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4607334 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4607333 A s t). Qed.
Lemma lem4607335 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term62 A s a t) = (term319 A s a t).
Proof. exact (@lem4607334 A (@DELETE A s a) t). Qed.
Lemma lem4607342 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term304 A s a t) = (term320 A s a t).
Proof. exact (MK_COMB (@lem4607331 A s t) (@lem4607335 A s a t)). Qed.
Lemma lem4607345 {A : Type'} (a : A) (t : A -> Prop) : (term305 A a t) = (term321 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607342 A s a t)). Qed.
Lemma lem4607346 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607347 {A : Type'} (a : A) (t : A -> Prop) : (term306 A a t) = (term322 A a t).
Proof. exact (MK_COMB (@lem4607346 A) (@lem4607345 A a t)). Qed.
Lemma lem4607352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607353 {A : Type'} (a : A) (t : A -> Prop) : (term307 A a t) = (term323 A a t).
Proof. exact (MK_COMB (@lem4607352) (@lem4607347 A a t)). Qed.
Lemma lem4607361 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4607362 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4607361 A s t). Qed.
Lemma lem4607369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term202 A s t) = (term318 A s t).
Proof. exact (MK_COMB (@lem4607369) (@lem4607362 A s t)). Qed.
Lemma lem4607372 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4607373 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4607372 A s t). Qed.
Lemma lem4607374 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term312 A s a t) = (term324 A s a t).
Proof. exact (@lem4607373 A (term325 A s a) t). Qed.
Lemma lem4607381 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term313 A s a t) = (term326 A s a t).
Proof. exact (MK_COMB (@lem4607370 A s t) (@lem4607374 A s a t)). Qed.
Lemma lem4607384 {A : Type'} (a : A) (t : A -> Prop) : (term314 A a t) = (term327 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607381 A s a t)). Qed.
Lemma lem4607385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607386 {A : Type'} (a : A) (t : A -> Prop) : (term315 A a t) = (term328 A a t).
Proof. exact (MK_COMB (@lem4607385 A) (@lem4607384 A a t)). Qed.
Lemma lem4607391 {A : Type'} (a : A) (t : A -> Prop) : (term316 A a t) = (term329 A a t).
Proof. exact (MK_COMB (@lem4607353 A a t) (@lem4607386 A a t)). Qed.
Lemma lem4607394 {A : Type'} (a : A) (t : A -> Prop) : (term329 A a t) = (term316 A a t).
Proof. exact (SYM (@lem4607391 A a t)). Qed.
Lemma lem4607410 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607411 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607410 A P x). Qed.
Lemma lem4607412 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4607411 A s x). Qed.
Lemma lem4607413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607414 {A : Type'} (s : A -> Prop) (x : A) : (term330 A x s) = (term331 A s x).
Proof. exact (MK_COMB (@lem4607413) (@lem4607412 A s x)). Qed.
Lemma lem4607416 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607417 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607416 A P x). Qed.
Lemma lem4607418 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4607417 A t x). Qed.
Lemma lem4607419 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term332 A s x t) = (term333 A s t x).
Proof. exact (MK_COMB (@lem4607414 A s x) (@lem4607418 A t x)). Qed.
Lemma lem4607422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term334 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4607419 A s t x)). Qed.
Lemma lem4607423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607424 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4607423 A) (@lem4607422 A s t)). Qed.
Lemma lem4607429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607430 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term337 A s t).
Proof. exact (MK_COMB (@lem4607429) (@lem4607424 A s t)). Qed.
Lemma lem4607438 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4607439 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4607438 A s x y). Qed.
Lemma lem4607440 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term339 A s x a).
Proof. exact (@lem4607439 A s x a). Qed.
Lemma lem4607444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607445 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607444 A P x). Qed.
Lemma lem4607446 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4607445 A s x). Qed.
Lemma lem4607447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607448 {A : Type'} (s : A -> Prop) (x : A) : (term340 A x s) = (term341 A s x).
Proof. exact (MK_COMB (@lem4607447) (@lem4607446 A s x)). Qed.
Lemma lem4607451 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4607452 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term339 A s x a) = (term343 A s x a).
Proof. exact (MK_COMB (@lem4607448 A s x) (@lem4607451 A x a)). Qed.
Lemma lem4607455 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term343 A s x a).
Proof. exact (TRANS (@lem4607440 A s x a) (@lem4607452 A s x a)). Qed.
Lemma lem4607456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607457 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term344 A x s a) = (term345 A s x a).
Proof. exact (MK_COMB (@lem4607456) (@lem4607455 A s x a)). Qed.
Lemma lem4607459 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607460 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607459 A P x). Qed.
Lemma lem4607461 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4607460 A t x). Qed.
Lemma lem4607462 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term346 A s a x t) = (term347 A s a t x).
Proof. exact (MK_COMB (@lem4607457 A s x a) (@lem4607461 A t x)). Qed.
Lemma lem4607465 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term348 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4607462 A s a t x)). Qed.
Lemma lem4607466 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607467 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term319 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4607466 A) (@lem4607465 A s a t)). Qed.
Lemma lem4607472 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term320 A s a t) = (term351 A s a t).
Proof. exact (MK_COMB (@lem4607430 A s t) (@lem4607467 A s a t)). Qed.
Lemma lem4607475 {A : Type'} (a : A) (t : A -> Prop) : (term321 A a t) = (term352 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607472 A s a t)). Qed.
Lemma lem4607476 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607477 {A : Type'} (a : A) (t : A -> Prop) : (term322 A a t) = (term353 A a t).
Proof. exact (MK_COMB (@lem4607476 A) (@lem4607475 A a t)). Qed.
Lemma lem4607482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607483 {A : Type'} (a : A) (t : A -> Prop) : (term323 A a t) = (term354 A a t).
Proof. exact (MK_COMB (@lem4607482) (@lem4607477 A a t)). Qed.
Lemma lem4607497 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607498 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607497 A P x). Qed.
Lemma lem4607499 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4607498 A s x). Qed.
Lemma lem4607500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607501 {A : Type'} (s : A -> Prop) (x : A) : (term330 A x s) = (term331 A s x).
Proof. exact (MK_COMB (@lem4607500) (@lem4607499 A s x)). Qed.
Lemma lem4607503 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607503 A P x). Qed.
Lemma lem4607505 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4607504 A t x). Qed.
Lemma lem4607506 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term332 A s x t) = (term333 A s t x).
Proof. exact (MK_COMB (@lem4607501 A s x) (@lem4607505 A t x)). Qed.
Lemma lem4607509 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term334 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4607506 A s t x)). Qed.
Lemma lem4607510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607511 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4607510 A) (@lem4607509 A s t)). Qed.
Lemma lem4607516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607517 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term337 A s t).
Proof. exact (MK_COMB (@lem4607516) (@lem4607511 A s t)). Qed.
Lemma lem4607525 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4607526 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4607525 A s x y). Qed.
Lemma lem4607527 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term355 A x s a) = (term356 A s x a).
Proof. exact (@lem4607526 A (@INSERT A a s) x a). Qed.
Lemma lem4607531 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4607532 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (@lem4607531 A y x s). Qed.
Lemma lem4607533 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term357 A x a s) = (term358 A a x s).
Proof. exact (@lem4607532 A a x s). Qed.
Lemma lem4607539 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607540 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607539 A P x). Qed.
Lemma lem4607541 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4607540 A s x). Qed.
Lemma lem4607542 {A : Type'} (x : A) (a : A) : (term359 A x a) = (term359 A x a).
Proof. exact (eq_refl (term359 A x a)). Qed.
Lemma lem4607543 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term358 A a x s) = (term360 A a s x).
Proof. exact (MK_COMB (@lem4607542 A x a) (@lem4607541 A s x)). Qed.
Lemma lem4607546 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term357 A x a s) = (term360 A a s x).
Proof. exact (TRANS (@lem4607533 A a x s) (@lem4607543 A a s x)). Qed.
Lemma lem4607547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607548 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term361 A x a s) = (term362 A a s x).
Proof. exact (MK_COMB (@lem4607547) (@lem4607546 A a s x)). Qed.
Lemma lem4607551 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4607552 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term356 A s x a) = (term363 A s x a).
Proof. exact (MK_COMB (@lem4607548 A a s x) (@lem4607551 A x a)). Qed.
Lemma lem4607555 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term355 A x s a) = (term363 A s x a).
Proof. exact (TRANS (@lem4607527 A s x a) (@lem4607552 A s x a)). Qed.
Lemma lem4607556 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607557 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term364 A x s a) = (term365 A s x a).
Proof. exact (MK_COMB (@lem4607556) (@lem4607555 A s x a)). Qed.
Lemma lem4607559 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4607560 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4607559 A P x). Qed.
Lemma lem4607561 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4607560 A t x). Qed.
Lemma lem4607562 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term366 A s a x t) = (term367 A s a t x).
Proof. exact (MK_COMB (@lem4607557 A s x a) (@lem4607561 A t x)). Qed.
Lemma lem4607565 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term368 A s a t) = (term369 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4607562 A s a t x)). Qed.
Lemma lem4607566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607567 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term324 A s a t) = (term370 A s a t).
Proof. exact (MK_COMB (@lem4607566 A) (@lem4607565 A s a t)). Qed.
Lemma lem4607572 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term326 A s a t) = (term371 A s a t).
Proof. exact (MK_COMB (@lem4607517 A s t) (@lem4607567 A s a t)). Qed.
Lemma lem4607575 {A : Type'} (a : A) (t : A -> Prop) : (term327 A a t) = (term372 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607572 A s a t)). Qed.
Lemma lem4607576 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607577 {A : Type'} (a : A) (t : A -> Prop) : (term328 A a t) = (term373 A a t).
Proof. exact (MK_COMB (@lem4607576 A) (@lem4607575 A a t)). Qed.
Lemma lem4607582 {A : Type'} (a : A) (t : A -> Prop) : (term329 A a t) = (term374 A a t).
Proof. exact (MK_COMB (@lem4607483 A a t) (@lem4607577 A a t)). Qed.
Lemma lem4607585 {A : Type'} (a : A) (t : A -> Prop) : (term374 A a t) = (term329 A a t).
Proof. exact (SYM (@lem4607582 A a t)). Qed.
Lemma lem4607587 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4607588 {A : Type'} (a : A) (t : A -> Prop) : (term374 A a t) = (term376 A a t).
Proof. exact (@lem4607587 (term374 A a t)). Qed.
Lemma lem4607589 {A : Type'} (a : A) (t : A -> Prop) : (term376 A a t) = (term374 A a t).
Proof. exact (SYM (@lem4607588 A a t)). Qed.
Lemma lem4607590 {A : Type'} (a : A) (t : A -> Prop) (h1 : term377 A a t) : term377 A a t.
Proof. exact (h1). Qed.
Lemma lem4607593 {A : Type'} (a : A) (t : A -> Prop) (h1 : term376 A a t) : term376 A a t.
Proof. exact (h1). Qed.
Lemma lem4607594 {A : Type'} (a : A) (t : A -> Prop) : term378 A a t.
Proof. exact (fun h0 : term376 A a t => @lem4607593 A a t h0). Qed.
Lemma lem4607595 {A : Type'} (a : A) (t : A -> Prop) (h1 : term378 A a t) : term378 A a t.
Proof. exact (h1). Qed.
Lemma lem4607596 {A : Type'} (a : A) (t : A -> Prop) (h1 : term376 A a t) : term376 A a t.
Proof. exact (h1). Qed.
Lemma lem4607597 {A : Type'} (a : A) (t : A -> Prop) (h1 : term376 A a t) (h2 : term378 A a t) : term376 A a t.
Proof. exact (@lem4607595 A a t h2 (@lem4607596 A a t h1)). Qed.
Lemma lem4607598 {A : Type'} (a : A) (t : A -> Prop) (h1 : term376 A a t) : term379 A a t.
Proof. exact (fun h0 : term378 A a t => @lem4607597 A a t h1 h0). Qed.
Lemma lem4607599 {A : Type'} (a : A) (t : A -> Prop) (h1 : term378 A a t) : term378 A a t.
Proof. exact (h1). Qed.
Lemma lem4607600 {A : Type'} (a : A) (t : A -> Prop) (h1 : term376 A a t) (h2 : term378 A a t) : term376 A a t.
Proof. exact (@lem4607598 A a t h1 (@lem4607599 A a t h2)). Qed.
Lemma lem4607601 {A : Type'} (a : A) (t : A -> Prop) (h1 : term378 A a t) : term378 A a t.
Proof. exact (fun h0 : term376 A a t => @lem4607600 A a t h0 h1). Qed.
Lemma lem4607602 {A : Type'} (a : A) (t : A -> Prop) : term380 A a t.
Proof. exact (fun h0 : term378 A a t => @lem4607601 A a t h0). Qed.
Lemma lem4607605 {A : Type'} (a : A) (t : A -> Prop) : term378 A a t.
Proof. exact (@lem4607602 A a t (@lem4607594 A a t)). Qed.
Lemma lem4607606 {A : Type'} (a : A) (t : A -> Prop) : term378 A a t.
Proof. exact (@lem4607605 A a t). Qed.
Lemma lem4607616 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4607617 {A : Type'} (a : A) (t : A -> Prop) : (term376 A a t) = (term381 A a t).
Proof. exact (@lem4607616 (term377 A a t)). Qed.
Lemma lem4607619 (t : Prop) : (term382 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4607620 {A : Type'} (a : A) (t : A -> Prop) : (term381 A a t) = (term374 A a t).
Proof. exact (@lem4607619 (term374 A a t)). Qed.
Lemma lem4607623 {A : Type'} (a : A) (t : A -> Prop) : (term376 A a t) = (term374 A a t).
Proof. exact (TRANS (@lem4607617 A a t) (@lem4607620 A a t)). Qed.
Lemma lem4607666 {A : Type'} (t : A -> Prop) : (term383 A t) = (term384 A t).
Proof. exact (fun_ext (fun a : A => @lem4607623 A a t)). Qed.
Lemma lem4607667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607668 {A : Type'} (t : A -> Prop) : (term385 A t) = (term386 A t).
Proof. exact (MK_COMB (@lem4607667 A) (@lem4607666 A t)). Qed.
Lemma lem4607670 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem4607671 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (@lem4607670 A P Q). Qed.
Lemma lem4607672 {A : Type'} (t : A -> Prop) : (term389 A t) = (term390 A t).
Proof. exact (@lem4607671 A (term391 A t) (term392 A t)). Qed.
Lemma lem4607673 {A : Type'} (a : A) (t : A -> Prop) : (term393 A t a) = (term353 A a t).
Proof. exact (eq_refl (term393 A t a)). Qed.
Lemma lem4607674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607675 {A : Type'} (a : A) (t : A -> Prop) : (term394 A t a) = (term354 A a t).
Proof. exact (MK_COMB (@lem4607674) (@lem4607673 A a t)). Qed.
Lemma lem4607676 {A : Type'} (a : A) (t : A -> Prop) : (term395 A t a) = (term373 A a t).
Proof. exact (eq_refl (term395 A t a)). Qed.
Lemma lem4607677 {A : Type'} (a : A) (t : A -> Prop) : (term396 A t a) = (term374 A a t).
Proof. exact (MK_COMB (@lem4607675 A a t) (@lem4607676 A a t)). Qed.
Lemma lem4607678 {A : Type'} (t : A -> Prop) : (term397 A t) = (term384 A t).
Proof. exact (fun_ext (fun a : A => @lem4607677 A a t)). Qed.
Lemma lem4607679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607680 {A : Type'} (t : A -> Prop) : (term389 A t) = (term386 A t).
Proof. exact (MK_COMB (@lem4607679 A) (@lem4607678 A t)). Qed.
Lemma lem4607681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607682 {A : Type'} (t : A -> Prop) : (term398 A t) = (term399 A t).
Proof. exact (MK_COMB (@lem4607681) (@lem4607680 A t)). Qed.
Lemma lem4607683 {A : Type'} (a : A) (t : A -> Prop) : (term393 A t a) = (term353 A a t).
Proof. exact (eq_refl (term393 A t a)). Qed.
Lemma lem4607684 {A : Type'} (t : A -> Prop) : (term400 A t) = (term391 A t).
Proof. exact (fun_ext (fun a : A => @lem4607683 A a t)). Qed.
Lemma lem4607685 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607686 {A : Type'} (t : A -> Prop) : (term401 A t) = (term402 A t).
Proof. exact (MK_COMB (@lem4607685 A) (@lem4607684 A t)). Qed.
Lemma lem4607687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607688 {A : Type'} (t : A -> Prop) : (term403 A t) = (term404 A t).
Proof. exact (MK_COMB (@lem4607687) (@lem4607686 A t)). Qed.
Lemma lem4607689 {A : Type'} (a : A) (t : A -> Prop) : (term395 A t a) = (term373 A a t).
Proof. exact (eq_refl (term395 A t a)). Qed.
Lemma lem4607690 {A : Type'} (t : A -> Prop) : (term405 A t) = (term392 A t).
Proof. exact (fun_ext (fun a : A => @lem4607689 A a t)). Qed.
Lemma lem4607691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607692 {A : Type'} (t : A -> Prop) : (term406 A t) = (term407 A t).
Proof. exact (MK_COMB (@lem4607691 A) (@lem4607690 A t)). Qed.
Lemma lem4607693 {A : Type'} (t : A -> Prop) : (term390 A t) = (term408 A t).
Proof. exact (MK_COMB (@lem4607688 A t) (@lem4607692 A t)). Qed.
Lemma lem4607694 {A : Type'} (t : A -> Prop) : ((term389 A t) = (term390 A t)) = ((term386 A t) = (term408 A t)).
Proof. exact (MK_COMB (@lem4607682 A t) (@lem4607693 A t)). Qed.
Lemma lem4607695 {A : Type'} (t : A -> Prop) : (term386 A t) = (term408 A t).
Proof. exact (EQ_MP (@lem4607694 A t) (@lem4607672 A t)). Qed.
Lemma lem4607748 {A : Type'} (t : A -> Prop) : (term385 A t) = (term408 A t).
Proof. exact (TRANS (@lem4607668 A t) (@lem4607695 A t)). Qed.
Lemma lem4607749 {A : Type'} : (term409 A) = (term410 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607748 A t)). Qed.
Lemma lem4607750 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607751 {A : Type'} : (term411 A) = (term412 A).
Proof. exact (MK_COMB (@lem4607750 A) (@lem4607749 A)). Qed.
Lemma lem4607753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem4607754 {A : Type'} (P : type686 A) (Q : type686 A) : (term413 A P Q) = (term414 A P Q).
Proof. exact (@lem4607753 (A -> Prop) P Q). Qed.
Lemma lem4607755 {A : Type'} : (term415 A) = (term416 A).
Proof. exact (@lem4607754 A (term417 A) (term418 A)). Qed.
Lemma lem4607756 {A : Type'} (t : A -> Prop) : (term419 A t) = (term402 A t).
Proof. exact (eq_refl (term419 A t)). Qed.
Lemma lem4607757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607758 {A : Type'} (t : A -> Prop) : (term420 A t) = (term404 A t).
Proof. exact (MK_COMB (@lem4607757) (@lem4607756 A t)). Qed.
Lemma lem4607759 {A : Type'} (t : A -> Prop) : (term421 A t) = (term407 A t).
Proof. exact (eq_refl (term421 A t)). Qed.
Lemma lem4607760 {A : Type'} (t : A -> Prop) : (term422 A t) = (term408 A t).
Proof. exact (MK_COMB (@lem4607758 A t) (@lem4607759 A t)). Qed.
Lemma lem4607761 {A : Type'} : (term423 A) = (term410 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607760 A t)). Qed.
Lemma lem4607762 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607763 {A : Type'} : (term415 A) = (term412 A).
Proof. exact (MK_COMB (@lem4607762 A) (@lem4607761 A)). Qed.
Lemma lem4607764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4607765 {A : Type'} : (term424 A) = (term425 A).
Proof. exact (MK_COMB (@lem4607764) (@lem4607763 A)). Qed.
Lemma lem4607766 {A : Type'} (t : A -> Prop) : (term419 A t) = (term402 A t).
Proof. exact (eq_refl (term419 A t)). Qed.
Lemma lem4607767 {A : Type'} : (term426 A) = (term417 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607766 A t)). Qed.
Lemma lem4607768 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607769 {A : Type'} : (term427 A) = (term428 A).
Proof. exact (MK_COMB (@lem4607768 A) (@lem4607767 A)). Qed.
Lemma lem4607770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607771 {A : Type'} : (term429 A) = (term430 A).
Proof. exact (MK_COMB (@lem4607770) (@lem4607769 A)). Qed.
Lemma lem4607772 {A : Type'} (t : A -> Prop) : (term421 A t) = (term407 A t).
Proof. exact (eq_refl (term421 A t)). Qed.
Lemma lem4607773 {A : Type'} : (term431 A) = (term418 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607772 A t)). Qed.
Lemma lem4607774 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607775 {A : Type'} : (term432 A) = (term433 A).
Proof. exact (MK_COMB (@lem4607774 A) (@lem4607773 A)). Qed.
Lemma lem4607776 {A : Type'} : (term416 A) = (term434 A).
Proof. exact (MK_COMB (@lem4607771 A) (@lem4607775 A)). Qed.
Lemma lem4607777 {A : Type'} : ((term415 A) = (term416 A)) = ((term412 A) = (term434 A)).
Proof. exact (MK_COMB (@lem4607765 A) (@lem4607776 A)). Qed.
Lemma lem4607778 {A : Type'} : (term412 A) = (term434 A).
Proof. exact (EQ_MP (@lem4607777 A) (@lem4607755 A)). Qed.
Lemma lem4607843 {A : Type'} : (term411 A) = (term434 A).
Proof. exact (TRANS (@lem4607751 A) (@lem4607778 A)). Qed.
Lemma lem4607858 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term367 A s a t x) = (term367 A s a t x).
Proof. exact (eq_refl (term367 A s a t x)). Qed.
Lemma lem4607859 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term369 A s a t) = (term369 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4607858 A s a t x)). Qed.
Lemma lem4607860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607861 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term370 A s a t) = (term370 A s a t).
Proof. exact (MK_COMB (@lem4607860 A) (@lem4607859 A s a t)). Qed.
Lemma lem4607866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term333 A s t x) = (term333 A s t x).
Proof. exact (eq_refl (term333 A s t x)). Qed.
Lemma lem4607867 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term335 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4607866 A s t x)). Qed.
Lemma lem4607868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607869 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term336 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4607868 A) (@lem4607867 A s t)). Qed.
Lemma lem4607870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607871 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term337 A s t) = (term337 A s t).
Proof. exact (MK_COMB (@lem4607870) (@lem4607869 A s t)). Qed.
Lemma lem4607872 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term371 A s a t) = (term371 A s a t).
Proof. exact (MK_COMB (@lem4607871 A s t) (@lem4607861 A s a t)). Qed.
Lemma lem4607873 {A : Type'} (a : A) (t : A -> Prop) : (term372 A a t) = (term372 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607872 A s a t)). Qed.
Lemma lem4607874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607875 {A : Type'} (a : A) (t : A -> Prop) : (term373 A a t) = (term373 A a t).
Proof. exact (MK_COMB (@lem4607874 A) (@lem4607873 A a t)). Qed.
Lemma lem4607876 {A : Type'} (t : A -> Prop) : (term392 A t) = (term392 A t).
Proof. exact (fun_ext (fun a : A => @lem4607875 A a t)). Qed.
Lemma lem4607877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607878 {A : Type'} (t : A -> Prop) : (term407 A t) = (term407 A t).
Proof. exact (MK_COMB (@lem4607877 A) (@lem4607876 A t)). Qed.
Lemma lem4607879 {A : Type'} : (term418 A) = (term418 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607878 A t)). Qed.
Lemma lem4607880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607881 {A : Type'} : (term433 A) = (term433 A).
Proof. exact (MK_COMB (@lem4607880 A) (@lem4607879 A)). Qed.
Lemma lem4607892 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term347 A s a t x)). Qed.
Lemma lem4607893 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4607892 A s a t x)). Qed.
Lemma lem4607894 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607895 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4607894 A) (@lem4607893 A s a t)). Qed.
Lemma lem4607900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term333 A s t x) = (term333 A s t x).
Proof. exact (eq_refl (term333 A s t x)). Qed.
Lemma lem4607901 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term335 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4607900 A s t x)). Qed.
Lemma lem4607902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607903 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term336 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4607902 A) (@lem4607901 A s t)). Qed.
Lemma lem4607904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4607905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term337 A s t) = (term337 A s t).
Proof. exact (MK_COMB (@lem4607904) (@lem4607903 A s t)). Qed.
Lemma lem4607906 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term351 A s a t) = (term351 A s a t).
Proof. exact (MK_COMB (@lem4607905 A s t) (@lem4607895 A s a t)). Qed.
Lemma lem4607907 {A : Type'} (a : A) (t : A -> Prop) : (term352 A a t) = (term352 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4607906 A s a t)). Qed.
Lemma lem4607908 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607909 {A : Type'} (a : A) (t : A -> Prop) : (term353 A a t) = (term353 A a t).
Proof. exact (MK_COMB (@lem4607908 A) (@lem4607907 A a t)). Qed.
Lemma lem4607910 {A : Type'} (t : A -> Prop) : (term391 A t) = (term391 A t).
Proof. exact (fun_ext (fun a : A => @lem4607909 A a t)). Qed.
Lemma lem4607911 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4607912 {A : Type'} (t : A -> Prop) : (term402 A t) = (term402 A t).
Proof. exact (MK_COMB (@lem4607911 A) (@lem4607910 A t)). Qed.
Lemma lem4607913 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4607912 A t)). Qed.
Lemma lem4607914 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4607915 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem4607914 A) (@lem4607913 A)). Qed.
Lemma lem4607916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4607917 {A : Type'} : (term430 A) = (term430 A).
Proof. exact (MK_COMB (@lem4607916) (@lem4607915 A)). Qed.
Lemma lem4607918 {A : Type'} : (term434 A) = (term434 A).
Proof. exact (MK_COMB (@lem4607917 A) (@lem4607881 A)). Qed.
Lemma lem4608001 {A : Type'} : (term411 A) = (term434 A).
Proof. exact (TRANS (@lem4607843 A) (@lem4607918 A)). Qed.
Lemma lem4608002 {A : Type'} : (term434 A) = (term411 A).
Proof. exact (SYM (@lem4608001 A)). Qed.
Lemma lem4608004 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4608005 {A : Type'} : (term434 A) = (term435 A).
Proof. exact (@lem4608004 (term434 A)). Qed.
Lemma lem4608006 {A : Type'} : (term435 A) = (term434 A).
Proof. exact (SYM (@lem4608005 A)). Qed.
Lemma lem4608007 {A : Type'} (h1 : term436 A) : term436 A.
Proof. exact (h1). Qed.
Lemma lem4608014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term333 A s t x) = (term437 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem4608015 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term335 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608014 A s t x)). Qed.
Lemma lem4608016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term336 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608016 A) (@lem4608015 A s t)). Qed.
Lemma lem4608028 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term440 A s a t x) = (term441 A s a t x).
Proof. exact (@lem17362 (term343 A s x a) (t x)). Qed.
Lemma lem4608029 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4608030 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term444 A s a t) = (term445 A s a t).
Proof. exact (@lem4608029 A (term349 A s a t)). Qed.
Lemma lem4608031 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term446 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term446 A s a t x)). Qed.
Lemma lem4608032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608033 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term447 A s a t x) = (term440 A s a t x).
Proof. exact (MK_COMB (@lem4608032) (@lem4608031 A s a t x)). Qed.
Lemma lem4608034 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term447 A s a t x) = (term441 A s a t x).
Proof. exact (TRANS (@lem4608033 A s a t x) (@lem4608028 A s a t x)). Qed.
Lemma lem4608035 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term448 A s a t) = (term449 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608034 A s a t x)). Qed.
Lemma lem4608036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608037 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term445 A s a t) = (term450 A s a t).
Proof. exact (MK_COMB (@lem4608036 A) (@lem4608035 A s a t)). Qed.
Lemma lem4608038 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term444 A s a t) = (term450 A s a t).
Proof. exact (TRANS (@lem4608030 A s a t) (@lem4608037 A s a t)). Qed.
Lemma lem4608039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4608040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term451 A s t) = (term452 A s t).
Proof. exact (MK_COMB (@lem4608039) (@lem4608017 A s t)). Qed.
Lemma lem4608041 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term453 A s a t) = (term454 A s a t).
Proof. exact (MK_COMB (@lem4608040 A s t) (@lem4608038 A s a t)). Qed.
Lemma lem4608042 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term455 A s a t) = (term453 A s a t).
Proof. exact (@lem17362 (term336 A s t) (term350 A s a t)). Qed.
Lemma lem4608043 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term455 A s a t) = (term454 A s a t).
Proof. exact (TRANS (@lem4608042 A s a t) (@lem4608041 A s a t)). Qed.
Lemma lem4608044 {A : Type'} (P : type686 A) : (term456 A P) = (term457 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4608045 {A : Type'} (a : A) (t : A -> Prop) : (term458 A a t) = (term459 A a t).
Proof. exact (@lem4608044 A (term352 A a t)). Qed.
Lemma lem4608046 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term460 A a t s) = (term351 A s a t).
Proof. exact (eq_refl (term460 A a t s)). Qed.
Lemma lem4608047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608048 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term461 A a t s) = (term455 A s a t).
Proof. exact (MK_COMB (@lem4608047) (@lem4608046 A s a t)). Qed.
Lemma lem4608049 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term461 A a t s) = (term454 A s a t).
Proof. exact (TRANS (@lem4608048 A s a t) (@lem4608043 A s a t)). Qed.
Lemma lem4608050 {A : Type'} (a : A) (t : A -> Prop) : (term462 A a t) = (term463 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608049 A s a t)). Qed.
Lemma lem4608051 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608052 {A : Type'} (a : A) (t : A -> Prop) : (term459 A a t) = (term464 A a t).
Proof. exact (MK_COMB (@lem4608051 A) (@lem4608050 A a t)). Qed.
Lemma lem4608053 {A : Type'} (a : A) (t : A -> Prop) : (term458 A a t) = (term464 A a t).
Proof. exact (TRANS (@lem4608045 A a t) (@lem4608052 A a t)). Qed.
Lemma lem4608054 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4608055 {A : Type'} (t : A -> Prop) : (term465 A t) = (term466 A t).
Proof. exact (@lem4608054 A (term391 A t)). Qed.
Lemma lem4608056 {A : Type'} (a : A) (t : A -> Prop) : (term393 A t a) = (term353 A a t).
Proof. exact (eq_refl (term393 A t a)). Qed.
Lemma lem4608057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608058 {A : Type'} (a : A) (t : A -> Prop) : (term467 A t a) = (term458 A a t).
Proof. exact (MK_COMB (@lem4608057) (@lem4608056 A a t)). Qed.
Lemma lem4608059 {A : Type'} (a : A) (t : A -> Prop) : (term467 A t a) = (term464 A a t).
Proof. exact (TRANS (@lem4608058 A a t) (@lem4608053 A a t)). Qed.
Lemma lem4608060 {A : Type'} (t : A -> Prop) : (term468 A t) = (term469 A t).
Proof. exact (fun_ext (fun a : A => @lem4608059 A a t)). Qed.
Lemma lem4608061 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608062 {A : Type'} (t : A -> Prop) : (term466 A t) = (term470 A t).
Proof. exact (MK_COMB (@lem4608061 A) (@lem4608060 A t)). Qed.
Lemma lem4608063 {A : Type'} (t : A -> Prop) : (term465 A t) = (term470 A t).
Proof. exact (TRANS (@lem4608055 A t) (@lem4608062 A t)). Qed.
Lemma lem4608064 {A : Type'} (P : type686 A) : (term456 A P) = (term457 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4608065 {A : Type'} : (term471 A) = (term472 A).
Proof. exact (@lem4608064 A (term417 A)). Qed.
Lemma lem4608066 {A : Type'} (t : A -> Prop) : (term419 A t) = (term402 A t).
Proof. exact (eq_refl (term419 A t)). Qed.
Lemma lem4608067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608068 {A : Type'} (t : A -> Prop) : (term473 A t) = (term465 A t).
Proof. exact (MK_COMB (@lem4608067) (@lem4608066 A t)). Qed.
Lemma lem4608069 {A : Type'} (t : A -> Prop) : (term473 A t) = (term470 A t).
Proof. exact (TRANS (@lem4608068 A t) (@lem4608063 A t)). Qed.
Lemma lem4608070 {A : Type'} : (term474 A) = (term475 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608069 A t)). Qed.
Lemma lem4608071 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608072 {A : Type'} : (term472 A) = (term476 A).
Proof. exact (MK_COMB (@lem4608071 A) (@lem4608070 A)). Qed.
Lemma lem4608073 {A : Type'} : (term471 A) = (term476 A).
Proof. exact (TRANS (@lem4608065 A) (@lem4608072 A)). Qed.
Lemma lem4608080 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term333 A s t x) = (term437 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem4608081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term335 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608080 A s t x)). Qed.
Lemma lem4608082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term336 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608082 A) (@lem4608081 A s t)). Qed.
Lemma lem4608098 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term477 A s a t x) = (term478 A s a t x).
Proof. exact (@lem17362 (term363 A s x a) (t x)). Qed.
Lemma lem4608099 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4608100 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term479 A s a t) = (term480 A s a t).
Proof. exact (@lem4608099 A (term369 A s a t)). Qed.
Lemma lem4608101 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term481 A s a t x) = (term367 A s a t x).
Proof. exact (eq_refl (term481 A s a t x)). Qed.
Lemma lem4608102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608103 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term482 A s a t x) = (term477 A s a t x).
Proof. exact (MK_COMB (@lem4608102) (@lem4608101 A s a t x)). Qed.
Lemma lem4608104 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term482 A s a t x) = (term478 A s a t x).
Proof. exact (TRANS (@lem4608103 A s a t x) (@lem4608098 A s a t x)). Qed.
Lemma lem4608105 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term483 A s a t) = (term484 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608104 A s a t x)). Qed.
Lemma lem4608106 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608107 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term480 A s a t) = (term485 A s a t).
Proof. exact (MK_COMB (@lem4608106 A) (@lem4608105 A s a t)). Qed.
Lemma lem4608108 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term479 A s a t) = (term485 A s a t).
Proof. exact (TRANS (@lem4608100 A s a t) (@lem4608107 A s a t)). Qed.
Lemma lem4608109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4608110 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term451 A s t) = (term452 A s t).
Proof. exact (MK_COMB (@lem4608109) (@lem4608083 A s t)). Qed.
Lemma lem4608111 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term486 A s a t) = (term487 A s a t).
Proof. exact (MK_COMB (@lem4608110 A s t) (@lem4608108 A s a t)). Qed.
Lemma lem4608112 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term488 A s a t) = (term486 A s a t).
Proof. exact (@lem17362 (term336 A s t) (term370 A s a t)). Qed.
Lemma lem4608113 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term488 A s a t) = (term487 A s a t).
Proof. exact (TRANS (@lem4608112 A s a t) (@lem4608111 A s a t)). Qed.
Lemma lem4608114 {A : Type'} (P : type686 A) : (term456 A P) = (term457 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4608115 {A : Type'} (a : A) (t : A -> Prop) : (term489 A a t) = (term490 A a t).
Proof. exact (@lem4608114 A (term372 A a t)). Qed.
Lemma lem4608116 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term491 A a t s) = (term371 A s a t).
Proof. exact (eq_refl (term491 A a t s)). Qed.
Lemma lem4608117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608118 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term492 A a t s) = (term488 A s a t).
Proof. exact (MK_COMB (@lem4608117) (@lem4608116 A s a t)). Qed.
Lemma lem4608119 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term492 A a t s) = (term487 A s a t).
Proof. exact (TRANS (@lem4608118 A s a t) (@lem4608113 A s a t)). Qed.
Lemma lem4608120 {A : Type'} (a : A) (t : A -> Prop) : (term493 A a t) = (term494 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608119 A s a t)). Qed.
Lemma lem4608121 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608122 {A : Type'} (a : A) (t : A -> Prop) : (term490 A a t) = (term495 A a t).
Proof. exact (MK_COMB (@lem4608121 A) (@lem4608120 A a t)). Qed.
Lemma lem4608123 {A : Type'} (a : A) (t : A -> Prop) : (term489 A a t) = (term495 A a t).
Proof. exact (TRANS (@lem4608115 A a t) (@lem4608122 A a t)). Qed.
Lemma lem4608124 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4608125 {A : Type'} (t : A -> Prop) : (term496 A t) = (term497 A t).
Proof. exact (@lem4608124 A (term392 A t)). Qed.
Lemma lem4608126 {A : Type'} (a : A) (t : A -> Prop) : (term395 A t a) = (term373 A a t).
Proof. exact (eq_refl (term395 A t a)). Qed.
Lemma lem4608127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608128 {A : Type'} (a : A) (t : A -> Prop) : (term498 A t a) = (term489 A a t).
Proof. exact (MK_COMB (@lem4608127) (@lem4608126 A a t)). Qed.
Lemma lem4608129 {A : Type'} (a : A) (t : A -> Prop) : (term498 A t a) = (term495 A a t).
Proof. exact (TRANS (@lem4608128 A a t) (@lem4608123 A a t)). Qed.
Lemma lem4608130 {A : Type'} (t : A -> Prop) : (term499 A t) = (term500 A t).
Proof. exact (fun_ext (fun a : A => @lem4608129 A a t)). Qed.
Lemma lem4608131 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608132 {A : Type'} (t : A -> Prop) : (term497 A t) = (term501 A t).
Proof. exact (MK_COMB (@lem4608131 A) (@lem4608130 A t)). Qed.
Lemma lem4608133 {A : Type'} (t : A -> Prop) : (term496 A t) = (term501 A t).
Proof. exact (TRANS (@lem4608125 A t) (@lem4608132 A t)). Qed.
Lemma lem4608134 {A : Type'} (P : type686 A) : (term456 A P) = (term457 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4608135 {A : Type'} : (term502 A) = (term503 A).
Proof. exact (@lem4608134 A (term418 A)). Qed.
Lemma lem4608136 {A : Type'} (t : A -> Prop) : (term421 A t) = (term407 A t).
Proof. exact (eq_refl (term421 A t)). Qed.
Lemma lem4608137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4608138 {A : Type'} (t : A -> Prop) : (term504 A t) = (term496 A t).
Proof. exact (MK_COMB (@lem4608137) (@lem4608136 A t)). Qed.
Lemma lem4608139 {A : Type'} (t : A -> Prop) : (term504 A t) = (term501 A t).
Proof. exact (TRANS (@lem4608138 A t) (@lem4608133 A t)). Qed.
Lemma lem4608140 {A : Type'} : (term505 A) = (term506 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608139 A t)). Qed.
Lemma lem4608141 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608142 {A : Type'} : (term503 A) = (term507 A).
Proof. exact (MK_COMB (@lem4608141 A) (@lem4608140 A)). Qed.
Lemma lem4608143 {A : Type'} : (term502 A) = (term507 A).
Proof. exact (TRANS (@lem4608135 A) (@lem4608142 A)). Qed.
Lemma lem4608144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608145 {A : Type'} : (term508 A) = (term509 A).
Proof. exact (MK_COMB (@lem4608144) (@lem4608073 A)). Qed.
Lemma lem4608146 {A : Type'} : (term510 A) = (term511 A).
Proof. exact (MK_COMB (@lem4608145 A) (@lem4608143 A)). Qed.
Lemma lem4608147 {A : Type'} : (term436 A) = (term510 A).
Proof. exact (@lem17045 (term428 A) (term433 A)). Qed.
Lemma lem4608148 {A : Type'} : (term436 A) = (term511 A).
Proof. exact (TRANS (@lem4608147 A) (@lem4608146 A)). Qed.
Lemma lem4608423 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4608424 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (@lem4608423 A P Q). Qed.
Lemma lem4608425 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term514 A s a t) = (term515 A s a t).
Proof. exact (@lem4608424 A (term439 A s t) (term449 A s a t)). Qed.
Lemma lem4608426 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term516 A s a t x) = (term441 A s a t x).
Proof. exact (eq_refl (term516 A s a t x)). Qed.
Lemma lem4608427 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term517 A s a t) = (term449 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608426 A s a t x)). Qed.
Lemma lem4608428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608429 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term518 A s a t) = (term450 A s a t).
Proof. exact (MK_COMB (@lem4608428 A) (@lem4608427 A s a t)). Qed.
Lemma lem4608430 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (eq_refl (term452 A s t)). Qed.
Lemma lem4608431 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term514 A s a t) = (term454 A s a t).
Proof. exact (MK_COMB (@lem4608430 A s t) (@lem4608429 A s a t)). Qed.
Lemma lem4608432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608433 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term519 A s a t) = (term520 A s a t).
Proof. exact (MK_COMB (@lem4608432) (@lem4608431 A s a t)). Qed.
Lemma lem4608434 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term516 A s a t x) = (term441 A s a t x).
Proof. exact (eq_refl (term516 A s a t x)). Qed.
Lemma lem4608435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (eq_refl (term452 A s t)). Qed.
Lemma lem4608436 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term521 A s a t x) = (term522 A s a t x).
Proof. exact (MK_COMB (@lem4608435 A s t) (@lem4608434 A s a t x)). Qed.
Lemma lem4608437 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term523 A s a t) = (term524 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608436 A s a t x)). Qed.
Lemma lem4608438 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608439 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term515 A s a t) = (term525 A s a t).
Proof. exact (MK_COMB (@lem4608438 A) (@lem4608437 A s a t)). Qed.
Lemma lem4608440 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term514 A s a t) = (term515 A s a t)) = ((term454 A s a t) = (term525 A s a t)).
Proof. exact (MK_COMB (@lem4608433 A s a t) (@lem4608439 A s a t)). Qed.
Lemma lem4608441 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term454 A s a t) = (term525 A s a t).
Proof. exact (EQ_MP (@lem4608440 A s a t) (@lem4608425 A s a t)). Qed.
Lemma lem4608442 {A : Type'} (a : A) (t : A -> Prop) : (term463 A a t) = (term526 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608441 A s a t)). Qed.
Lemma lem4608443 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608444 {A : Type'} (a : A) (t : A -> Prop) : (term464 A a t) = (term527 A a t).
Proof. exact (MK_COMB (@lem4608443 A) (@lem4608442 A a t)). Qed.
Lemma lem4608445 {A : Type'} (t : A -> Prop) : (term469 A t) = (term528 A t).
Proof. exact (fun_ext (fun a : A => @lem4608444 A a t)). Qed.
Lemma lem4608446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608447 {A : Type'} (t : A -> Prop) : (term470 A t) = (term529 A t).
Proof. exact (MK_COMB (@lem4608446 A) (@lem4608445 A t)). Qed.
Lemma lem4608448 {A : Type'} : (term475 A) = (term530 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608447 A t)). Qed.
Lemma lem4608449 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608450 {A : Type'} : (term476 A) = (term531 A).
Proof. exact (MK_COMB (@lem4608449 A) (@lem4608448 A)). Qed.
Lemma lem4608451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608452 {A : Type'} : (term509 A) = (term532 A).
Proof. exact (MK_COMB (@lem4608451) (@lem4608450 A)). Qed.
Lemma lem4608454 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4608455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (@lem4608454 A P Q). Qed.
Lemma lem4608456 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term533 A s a t) = (term534 A s a t).
Proof. exact (@lem4608455 A (term439 A s t) (term484 A s a t)). Qed.
Lemma lem4608457 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term535 A s a t x) = (term478 A s a t x).
Proof. exact (eq_refl (term535 A s a t x)). Qed.
Lemma lem4608458 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term536 A s a t) = (term484 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608457 A s a t x)). Qed.
Lemma lem4608459 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608460 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term537 A s a t) = (term485 A s a t).
Proof. exact (MK_COMB (@lem4608459 A) (@lem4608458 A s a t)). Qed.
Lemma lem4608461 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (eq_refl (term452 A s t)). Qed.
Lemma lem4608462 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term533 A s a t) = (term487 A s a t).
Proof. exact (MK_COMB (@lem4608461 A s t) (@lem4608460 A s a t)). Qed.
Lemma lem4608463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608464 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term538 A s a t) = (term539 A s a t).
Proof. exact (MK_COMB (@lem4608463) (@lem4608462 A s a t)). Qed.
Lemma lem4608465 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term535 A s a t x) = (term478 A s a t x).
Proof. exact (eq_refl (term535 A s a t x)). Qed.
Lemma lem4608466 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (eq_refl (term452 A s t)). Qed.
Lemma lem4608467 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term540 A s a t x) = (term541 A s a t x).
Proof. exact (MK_COMB (@lem4608466 A s t) (@lem4608465 A s a t x)). Qed.
Lemma lem4608468 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term542 A s a t) = (term543 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608467 A s a t x)). Qed.
Lemma lem4608469 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608470 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term534 A s a t) = (term544 A s a t).
Proof. exact (MK_COMB (@lem4608469 A) (@lem4608468 A s a t)). Qed.
Lemma lem4608471 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term533 A s a t) = (term534 A s a t)) = ((term487 A s a t) = (term544 A s a t)).
Proof. exact (MK_COMB (@lem4608464 A s a t) (@lem4608470 A s a t)). Qed.
Lemma lem4608472 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term487 A s a t) = (term544 A s a t).
Proof. exact (EQ_MP (@lem4608471 A s a t) (@lem4608456 A s a t)). Qed.
Lemma lem4608473 {A : Type'} (a : A) (t : A -> Prop) : (term494 A a t) = (term545 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608472 A s a t)). Qed.
Lemma lem4608474 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608475 {A : Type'} (a : A) (t : A -> Prop) : (term495 A a t) = (term546 A a t).
Proof. exact (MK_COMB (@lem4608474 A) (@lem4608473 A a t)). Qed.
Lemma lem4608476 {A : Type'} (t : A -> Prop) : (term500 A t) = (term547 A t).
Proof. exact (fun_ext (fun a : A => @lem4608475 A a t)). Qed.
Lemma lem4608477 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608478 {A : Type'} (t : A -> Prop) : (term501 A t) = (term548 A t).
Proof. exact (MK_COMB (@lem4608477 A) (@lem4608476 A t)). Qed.
Lemma lem4608479 {A : Type'} : (term506 A) = (term549 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608478 A t)). Qed.
Lemma lem4608480 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608481 {A : Type'} : (term507 A) = (term550 A).
Proof. exact (MK_COMB (@lem4608480 A) (@lem4608479 A)). Qed.
Lemma lem4608482 {A : Type'} : (term511 A) = (term551 A).
Proof. exact (MK_COMB (@lem4608452 A) (@lem4608481 A)). Qed.
Lemma lem4608484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4608485 {A : Type'} (P : type686 A) (Q : type686 A) : (term554 A P Q) = (term555 A P Q).
Proof. exact (@lem4608484 (A -> Prop) P Q). Qed.
Lemma lem4608486 {A : Type'} : (term556 A) = (term557 A).
Proof. exact (@lem4608485 A (term530 A) (term549 A)). Qed.
Lemma lem4608487 {A : Type'} (t : A -> Prop) : (term558 A t) = (term529 A t).
Proof. exact (eq_refl (term558 A t)). Qed.
Lemma lem4608488 {A : Type'} : (term559 A) = (term530 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608487 A t)). Qed.
Lemma lem4608489 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608490 {A : Type'} : (term560 A) = (term531 A).
Proof. exact (MK_COMB (@lem4608489 A) (@lem4608488 A)). Qed.
Lemma lem4608491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608492 {A : Type'} : (term561 A) = (term532 A).
Proof. exact (MK_COMB (@lem4608491) (@lem4608490 A)). Qed.
Lemma lem4608493 {A : Type'} (t : A -> Prop) : (term562 A t) = (term548 A t).
Proof. exact (eq_refl (term562 A t)). Qed.
Lemma lem4608494 {A : Type'} : (term563 A) = (term549 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608493 A t)). Qed.
Lemma lem4608495 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608496 {A : Type'} : (term564 A) = (term550 A).
Proof. exact (MK_COMB (@lem4608495 A) (@lem4608494 A)). Qed.
Lemma lem4608497 {A : Type'} : (term556 A) = (term551 A).
Proof. exact (MK_COMB (@lem4608492 A) (@lem4608496 A)). Qed.
Lemma lem4608498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608499 {A : Type'} : (term565 A) = (term566 A).
Proof. exact (MK_COMB (@lem4608498) (@lem4608497 A)). Qed.
Lemma lem4608500 {A : Type'} (t : A -> Prop) : (term558 A t) = (term529 A t).
Proof. exact (eq_refl (term558 A t)). Qed.
Lemma lem4608501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608502 {A : Type'} (t : A -> Prop) : (term567 A t) = (term568 A t).
Proof. exact (MK_COMB (@lem4608501) (@lem4608500 A t)). Qed.
Lemma lem4608503 {A : Type'} (t : A -> Prop) : (term562 A t) = (term548 A t).
Proof. exact (eq_refl (term562 A t)). Qed.
Lemma lem4608504 {A : Type'} (t : A -> Prop) : (term569 A t) = (term570 A t).
Proof. exact (MK_COMB (@lem4608502 A t) (@lem4608503 A t)). Qed.
Lemma lem4608505 {A : Type'} : (term571 A) = (term572 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608504 A t)). Qed.
Lemma lem4608506 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608507 {A : Type'} : (term557 A) = (term573 A).
Proof. exact (MK_COMB (@lem4608506 A) (@lem4608505 A)). Qed.
Lemma lem4608508 {A : Type'} : ((term556 A) = (term557 A)) = ((term551 A) = (term573 A)).
Proof. exact (MK_COMB (@lem4608499 A) (@lem4608507 A)). Qed.
Lemma lem4608509 {A : Type'} : (term551 A) = (term573 A).
Proof. exact (EQ_MP (@lem4608508 A) (@lem4608486 A)). Qed.
Lemma lem4608511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4608512 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (@lem4608511 A P Q). Qed.
Lemma lem4608513 {A : Type'} (t : A -> Prop) : (term574 A t) = (term575 A t).
Proof. exact (@lem4608512 A (term528 A t) (term547 A t)). Qed.
Lemma lem4608514 {A : Type'} (a : A) (t : A -> Prop) : (term576 A t a) = (term527 A a t).
Proof. exact (eq_refl (term576 A t a)). Qed.
Lemma lem4608515 {A : Type'} (t : A -> Prop) : (term577 A t) = (term528 A t).
Proof. exact (fun_ext (fun a : A => @lem4608514 A a t)). Qed.
Lemma lem4608516 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608517 {A : Type'} (t : A -> Prop) : (term578 A t) = (term529 A t).
Proof. exact (MK_COMB (@lem4608516 A) (@lem4608515 A t)). Qed.
Lemma lem4608518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608519 {A : Type'} (t : A -> Prop) : (term579 A t) = (term568 A t).
Proof. exact (MK_COMB (@lem4608518) (@lem4608517 A t)). Qed.
Lemma lem4608520 {A : Type'} (a : A) (t : A -> Prop) : (term580 A t a) = (term546 A a t).
Proof. exact (eq_refl (term580 A t a)). Qed.
Lemma lem4608521 {A : Type'} (t : A -> Prop) : (term581 A t) = (term547 A t).
Proof. exact (fun_ext (fun a : A => @lem4608520 A a t)). Qed.
Lemma lem4608522 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608523 {A : Type'} (t : A -> Prop) : (term582 A t) = (term548 A t).
Proof. exact (MK_COMB (@lem4608522 A) (@lem4608521 A t)). Qed.
Lemma lem4608524 {A : Type'} (t : A -> Prop) : (term574 A t) = (term570 A t).
Proof. exact (MK_COMB (@lem4608519 A t) (@lem4608523 A t)). Qed.
Lemma lem4608525 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608526 {A : Type'} (t : A -> Prop) : (term583 A t) = (term584 A t).
Proof. exact (MK_COMB (@lem4608525) (@lem4608524 A t)). Qed.
Lemma lem4608527 {A : Type'} (a : A) (t : A -> Prop) : (term576 A t a) = (term527 A a t).
Proof. exact (eq_refl (term576 A t a)). Qed.
Lemma lem4608528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608529 {A : Type'} (a : A) (t : A -> Prop) : (term585 A t a) = (term586 A a t).
Proof. exact (MK_COMB (@lem4608528) (@lem4608527 A a t)). Qed.
Lemma lem4608530 {A : Type'} (a : A) (t : A -> Prop) : (term580 A t a) = (term546 A a t).
Proof. exact (eq_refl (term580 A t a)). Qed.
Lemma lem4608531 {A : Type'} (a : A) (t : A -> Prop) : (term587 A t a) = (term588 A a t).
Proof. exact (MK_COMB (@lem4608529 A a t) (@lem4608530 A a t)). Qed.
Lemma lem4608532 {A : Type'} (t : A -> Prop) : (term589 A t) = (term590 A t).
Proof. exact (fun_ext (fun a : A => @lem4608531 A a t)). Qed.
Lemma lem4608533 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608534 {A : Type'} (t : A -> Prop) : (term575 A t) = (term591 A t).
Proof. exact (MK_COMB (@lem4608533 A) (@lem4608532 A t)). Qed.
Lemma lem4608535 {A : Type'} (t : A -> Prop) : ((term574 A t) = (term575 A t)) = ((term570 A t) = (term591 A t)).
Proof. exact (MK_COMB (@lem4608526 A t) (@lem4608534 A t)). Qed.
Lemma lem4608536 {A : Type'} (t : A -> Prop) : (term570 A t) = (term591 A t).
Proof. exact (EQ_MP (@lem4608535 A t) (@lem4608513 A t)). Qed.
Lemma lem4608538 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4608539 {A : Type'} (P : type686 A) (Q : type686 A) : (term554 A P Q) = (term555 A P Q).
Proof. exact (@lem4608538 (A -> Prop) P Q). Qed.
Lemma lem4608540 {A : Type'} (a : A) (t : A -> Prop) : (term592 A a t) = (term593 A a t).
Proof. exact (@lem4608539 A (term526 A a t) (term545 A a t)). Qed.
Lemma lem4608541 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term594 A a t s) = (term525 A s a t).
Proof. exact (eq_refl (term594 A a t s)). Qed.
Lemma lem4608542 {A : Type'} (a : A) (t : A -> Prop) : (term595 A a t) = (term526 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608541 A s a t)). Qed.
Lemma lem4608543 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608544 {A : Type'} (a : A) (t : A -> Prop) : (term596 A a t) = (term527 A a t).
Proof. exact (MK_COMB (@lem4608543 A) (@lem4608542 A a t)). Qed.
Lemma lem4608545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608546 {A : Type'} (a : A) (t : A -> Prop) : (term597 A a t) = (term586 A a t).
Proof. exact (MK_COMB (@lem4608545) (@lem4608544 A a t)). Qed.
Lemma lem4608547 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term598 A a t s) = (term544 A s a t).
Proof. exact (eq_refl (term598 A a t s)). Qed.
Lemma lem4608548 {A : Type'} (a : A) (t : A -> Prop) : (term599 A a t) = (term545 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608547 A s a t)). Qed.
Lemma lem4608549 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608550 {A : Type'} (a : A) (t : A -> Prop) : (term600 A a t) = (term546 A a t).
Proof. exact (MK_COMB (@lem4608549 A) (@lem4608548 A a t)). Qed.
Lemma lem4608551 {A : Type'} (a : A) (t : A -> Prop) : (term592 A a t) = (term588 A a t).
Proof. exact (MK_COMB (@lem4608546 A a t) (@lem4608550 A a t)). Qed.
Lemma lem4608552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608553 {A : Type'} (a : A) (t : A -> Prop) : (term601 A a t) = (term602 A a t).
Proof. exact (MK_COMB (@lem4608552) (@lem4608551 A a t)). Qed.
Lemma lem4608554 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term594 A a t s) = (term525 A s a t).
Proof. exact (eq_refl (term594 A a t s)). Qed.
Lemma lem4608555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608556 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term603 A a t s) = (term604 A s a t).
Proof. exact (MK_COMB (@lem4608555) (@lem4608554 A s a t)). Qed.
Lemma lem4608557 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term598 A a t s) = (term544 A s a t).
Proof. exact (eq_refl (term598 A a t s)). Qed.
Lemma lem4608558 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term605 A a t s) = (term606 A s a t).
Proof. exact (MK_COMB (@lem4608556 A s a t) (@lem4608557 A s a t)). Qed.
Lemma lem4608559 {A : Type'} (a : A) (t : A -> Prop) : (term607 A a t) = (term608 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608558 A s a t)). Qed.
Lemma lem4608560 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608561 {A : Type'} (a : A) (t : A -> Prop) : (term593 A a t) = (term609 A a t).
Proof. exact (MK_COMB (@lem4608560 A) (@lem4608559 A a t)). Qed.
Lemma lem4608562 {A : Type'} (a : A) (t : A -> Prop) : ((term592 A a t) = (term593 A a t)) = ((term588 A a t) = (term609 A a t)).
Proof. exact (MK_COMB (@lem4608553 A a t) (@lem4608561 A a t)). Qed.
Lemma lem4608563 {A : Type'} (a : A) (t : A -> Prop) : (term588 A a t) = (term609 A a t).
Proof. exact (EQ_MP (@lem4608562 A a t) (@lem4608540 A a t)). Qed.
Lemma lem4608565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4608566 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (@lem4608565 A P Q). Qed.
Lemma lem4608567 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term610 A s a t) = (term611 A s a t).
Proof. exact (@lem4608566 A (term524 A s a t) (term543 A s a t)). Qed.
Lemma lem4608568 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term612 A s a t x) = (term522 A s a t x).
Proof. exact (eq_refl (term612 A s a t x)). Qed.
Lemma lem4608569 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term613 A s a t) = (term524 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608568 A s a t x)). Qed.
Lemma lem4608570 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608571 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term614 A s a t) = (term525 A s a t).
Proof. exact (MK_COMB (@lem4608570 A) (@lem4608569 A s a t)). Qed.
Lemma lem4608572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608573 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term615 A s a t) = (term604 A s a t).
Proof. exact (MK_COMB (@lem4608572) (@lem4608571 A s a t)). Qed.
Lemma lem4608574 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term616 A s a t x) = (term541 A s a t x).
Proof. exact (eq_refl (term616 A s a t x)). Qed.
Lemma lem4608575 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term617 A s a t) = (term543 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608574 A s a t x)). Qed.
Lemma lem4608576 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608577 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term618 A s a t) = (term544 A s a t).
Proof. exact (MK_COMB (@lem4608576 A) (@lem4608575 A s a t)). Qed.
Lemma lem4608578 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term610 A s a t) = (term606 A s a t).
Proof. exact (MK_COMB (@lem4608573 A s a t) (@lem4608577 A s a t)). Qed.
Lemma lem4608579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608580 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term619 A s a t) = (term620 A s a t).
Proof. exact (MK_COMB (@lem4608579) (@lem4608578 A s a t)). Qed.
Lemma lem4608581 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term612 A s a t x) = (term522 A s a t x).
Proof. exact (eq_refl (term612 A s a t x)). Qed.
Lemma lem4608582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608583 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term621 A s a t x) = (term622 A s a t x).
Proof. exact (MK_COMB (@lem4608582) (@lem4608581 A s a t x)). Qed.
Lemma lem4608584 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term616 A s a t x) = (term541 A s a t x).
Proof. exact (eq_refl (term616 A s a t x)). Qed.
Lemma lem4608585 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term623 A s a t x) = (term624 A s a t x).
Proof. exact (MK_COMB (@lem4608583 A s a t x) (@lem4608584 A s a t x)). Qed.
Lemma lem4608586 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term625 A s a t) = (term626 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4608585 A s a t x)). Qed.
Lemma lem4608587 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608588 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term611 A s a t) = (term627 A s a t).
Proof. exact (MK_COMB (@lem4608587 A) (@lem4608586 A s a t)). Qed.
Lemma lem4608589 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term610 A s a t) = (term611 A s a t)) = ((term606 A s a t) = (term627 A s a t)).
Proof. exact (MK_COMB (@lem4608580 A s a t) (@lem4608588 A s a t)). Qed.
Lemma lem4608590 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term606 A s a t) = (term627 A s a t).
Proof. exact (EQ_MP (@lem4608589 A s a t) (@lem4608567 A s a t)). Qed.
Lemma lem4608591 {A : Type'} (a : A) (t : A -> Prop) : (term608 A a t) = (term628 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4608590 A s a t)). Qed.
Lemma lem4608592 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608593 {A : Type'} (a : A) (t : A -> Prop) : (term609 A a t) = (term629 A a t).
Proof. exact (MK_COMB (@lem4608592 A) (@lem4608591 A a t)). Qed.
Lemma lem4608594 {A : Type'} (a : A) (t : A -> Prop) : (term588 A a t) = (term629 A a t).
Proof. exact (TRANS (@lem4608563 A a t) (@lem4608593 A a t)). Qed.
Lemma lem4608595 {A : Type'} (t : A -> Prop) : (term590 A t) = (term630 A t).
Proof. exact (fun_ext (fun a : A => @lem4608594 A a t)). Qed.
Lemma lem4608596 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4608597 {A : Type'} (t : A -> Prop) : (term591 A t) = (term631 A t).
Proof. exact (MK_COMB (@lem4608596 A) (@lem4608595 A t)). Qed.
Lemma lem4608598 {A : Type'} (t : A -> Prop) : (term570 A t) = (term631 A t).
Proof. exact (TRANS (@lem4608536 A t) (@lem4608597 A t)). Qed.
Lemma lem4608599 {A : Type'} : (term572 A) = (term632 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4608598 A t)). Qed.
Lemma lem4608600 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4608601 {A : Type'} : (term573 A) = (term633 A).
Proof. exact (MK_COMB (@lem4608600 A) (@lem4608599 A)). Qed.
Lemma lem4608602 {A : Type'} : (term551 A) = (term633 A).
Proof. exact (TRANS (@lem4608509 A) (@lem4608601 A)). Qed.
Lemma lem4608604 {A : Type'} : (term511 A) = (term633 A).
Proof. exact (TRANS (@lem4608482 A) (@lem4608602 A)). Qed.
Lemma lem4608605 {A : Type'} : (term436 A) = (term633 A).
Proof. exact (TRANS (@lem4608148 A) (@lem4608604 A)). Qed.
Lemma lem4608606 {A : Type'} (h1 : term436 A) : term633 A.
Proof. exact (EQ_MP (@lem4608605 A) (@lem4608007 A h1)). Qed.
Lemma lem4608607 {A : Type'} (t : A -> Prop) (h1 : term631 A t) : term631 A t.
Proof. exact (h1). Qed.
Lemma lem4608608 {A : Type'} (a : A) (t : A -> Prop) (h1 : term629 A a t) : term629 A a t.
Proof. exact (h1). Qed.
Lemma lem4608609 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term627 A s a t) : term627 A s a t.
Proof. exact (h1). Qed.
Lemma lem4608610 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term624 A s a t x) : term624 A s a t x.
Proof. exact (h1). Qed.
Lemma lem4608639 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term478 A s a t x) = (term478 A s a t x).
Proof. exact (eq_refl (term478 A s a t x)). Qed.
Lemma lem4608650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term437 A s t x) = (term437 A s t x).
Proof. exact (eq_refl (term437 A s t x)). Qed.
Lemma lem4608651 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term438 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608650 A s t x)). Qed.
Lemma lem4608652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608653 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term439 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608652 A) (@lem4608651 A s t)). Qed.
Lemma lem4608654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4608655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (MK_COMB (@lem4608654) (@lem4608653 A s t)). Qed.
Lemma lem4608656 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term541 A s a t x) = (term541 A s a t x).
Proof. exact (MK_COMB (@lem4608655 A s t) (@lem4608639 A s a t x)). Qed.
Lemma lem4608677 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term441 A s a t x) = (term441 A s a t x).
Proof. exact (eq_refl (term441 A s a t x)). Qed.
Lemma lem4608688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term437 A s t x) = (term437 A s t x).
Proof. exact (eq_refl (term437 A s t x)). Qed.
Lemma lem4608689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term438 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608688 A s t x)). Qed.
Lemma lem4608690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608691 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term439 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608690 A) (@lem4608689 A s t)). Qed.
Lemma lem4608692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4608693 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term452 A s t) = (term452 A s t).
Proof. exact (MK_COMB (@lem4608692) (@lem4608691 A s t)). Qed.
Lemma lem4608694 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term522 A s a t x) = (term522 A s a t x).
Proof. exact (MK_COMB (@lem4608693 A s t) (@lem4608677 A s a t x)). Qed.
Lemma lem4608695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4608696 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term622 A s a t x) = (term622 A s a t x).
Proof. exact (MK_COMB (@lem4608695) (@lem4608694 A s a t x)). Qed.
Lemma lem4608697 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term624 A s a t x) = (term624 A s a t x).
Proof. exact (MK_COMB (@lem4608696 A s a t x) (@lem4608656 A s a t x)). Qed.
Lemma lem4608698 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term624 A s a t x) : term624 A s a t x.
Proof. exact (EQ_MP (@lem4608697 A s a t x) (@lem4608610 A s a t x h1)). Qed.
Lemma lem4608699 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term522 A s a t x.
Proof. exact (h1). Qed.
Lemma lem4608700 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term541 A s a t x.
Proof. exact (h1). Qed.
Lemma lem4608701 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term441 A s a t x.
Proof. exact (proj2 (@lem4608699 A s a t x h1)). Qed.
Lemma lem4608702 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term439 A s t.
Proof. exact (proj1 (@lem4608699 A s a t x h1)). Qed.
Lemma lem4608704 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term343 A s x a.
Proof. exact (proj1 (@lem4608701 A s a t x h1)). Qed.
Lemma lem4608707 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term478 A s a t x.
Proof. exact (proj2 (@lem4608700 A s a t x h1)). Qed.
Lemma lem4608708 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term439 A s t.
Proof. exact (proj1 (@lem4608700 A s a t x h1)). Qed.
Lemma lem4608710 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term363 A s x a.
Proof. exact (proj1 (@lem4608707 A s a t x h1)). Qed.
Lemma lem4608712 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term360 A a s x.
Proof. exact (proj1 (@lem4608710 A s a t x h1)). Qed.
Lemma lem4608722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term437 A s t x) = (term437 A s t x).
Proof. exact (eq_refl (term437 A s t x)). Qed.
Lemma lem4608723 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term438 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608722 A s t x)). Qed.
Lemma lem4608724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608726 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term439 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608724 A) (@lem4608723 A s t)). Qed.
Lemma lem4608727 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term439 A s t.
Proof. exact (EQ_MP (@lem4608726 A s t) (@lem4608702 A s a t x h1)). Qed.
Lemma lem4608764 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4608772 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term437 A s t x) = (term437 A s t x).
Proof. exact (eq_refl (term437 A s t x)). Qed.
Lemma lem4608773 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term438 A s t) = (term438 A s t).
Proof. exact (fun_ext (fun x : A => @lem4608772 A s t x)). Qed.
Lemma lem4608774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4608776 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term439 A s t) = (term439 A s t).
Proof. exact (MK_COMB (@lem4608774 A) (@lem4608773 A s t)). Qed.
Lemma lem4608777 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term439 A s t.
Proof. exact (EQ_MP (@lem4608776 A s t) (@lem4608708 A s a t x h1)). Qed.
Lemma lem4608789 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4608790 {A : Type'} (_55361 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term634 A s t _55361.
Proof. exact (@lem4608727 A s a t x h1 _55361). Qed.
Lemma lem4608791 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55361 : A) : (term634 A s t _55361) = (term437 A s t _55361).
Proof. exact (eq_refl (term634 A s t _55361)). Qed.
Lemma lem4608796 {A : Type'} (_55363 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term634 A s t _55363.
Proof. exact (@lem4608777 A s a t x h1 _55363). Qed.
Lemma lem4608797 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55363 : A) : (term634 A s t _55363) = (term437 A s t _55363).
Proof. exact (eq_refl (term634 A s t _55363)). Qed.
Lemma lem4608804 {A : Type'} (_55361 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term437 A s t _55361.
Proof. exact (EQ_MP (@lem4608791 A s t _55361) (@lem4608790 A _55361 s a t x h1)). Qed.
Lemma lem4608806 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term635 A t x.
Proof. exact (proj2 (@lem4608701 A s a t x h1)). Qed.
Lemma lem4608820 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term342 A x a.
Proof. exact (proj2 (@lem4608710 A s a t x h1)). Qed.
Lemma lem4608822 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4608828 {A : Type'} (_55363 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term437 A s t _55363.
Proof. exact (EQ_MP (@lem4608797 A s t _55363) (@lem4608796 A _55363 s a t x h1)). Qed.
Lemma lem4608830 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term635 A t x.
Proof. exact (proj2 (@lem4608707 A s a t x h1)). Qed.
Lemma lem4608834 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4608876 {A : Type'} (a : A) : (term636 A a) = (term636 A a).
Proof. exact (eq_refl (term636 A a)). Qed.
Lemma lem4608877 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term637 A a x) = (term638 A a).
Proof. exact (MK_COMB (@lem4608876 A a) (@lem4608822 A x a h1)). Qed.
Lemma lem4608878 {A : Type'} (a : A) : (term638 A a) = (term639 A a).
Proof. exact (eq_refl (term638 A a)). Qed.
Lemma lem4608879 {A : Type'} (a : A) (x : A) : (term640 A a x) = (term640 A a x).
Proof. exact (eq_refl (term640 A a x)). Qed.
Lemma lem4608880 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term638 A a)) = ((term637 A a x) = (term639 A a)).
Proof. exact (MK_COMB (@lem4608879 A a x) (@lem4608878 A a)). Qed.
Lemma lem4608881 {A : Type'} (x : A) (a : A) : (term637 A a x) = (term342 A x a).
Proof. exact (eq_refl (term637 A a x)). Qed.
Lemma lem4608882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608883 {A : Type'} (x : A) (a : A) : (term640 A a x) = (term641 A x a).
Proof. exact (MK_COMB (@lem4608882) (@lem4608881 A x a)). Qed.
Lemma lem4608884 {A : Type'} (a : A) : (term639 A a) = (term639 A a).
Proof. exact (eq_refl (term639 A a)). Qed.
Lemma lem4608885 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term639 A a)) = ((term342 A x a) = (term639 A a)).
Proof. exact (MK_COMB (@lem4608883 A x a) (@lem4608884 A a)). Qed.
Lemma lem4608886 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term638 A a)) = ((term342 A x a) = (term639 A a)).
Proof. exact (TRANS (@lem4608880 A x a) (@lem4608885 A x a)). Qed.
Lemma lem4608887 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term342 A x a) = (term639 A a).
Proof. exact (EQ_MP (@lem4608886 A x a) (@lem4608877 A x a h1)). Qed.
Lemma lem4608888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : term639 A a.
Proof. exact (EQ_MP (@lem4608887 A x a h2) (@lem4608820 A s a t x h1)). Qed.
Lemma lem4608916 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : s x.
Proof. exact (proj1 (@lem4608704 A s a t x h1)). Qed.
Lemma lem4608917 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term642 A s x.
Proof. exact (fun h0 : term635 A s x => @lem4608916 A s a t x h1). Qed.
Lemma lem4608919 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4608920 {A : Type'} (s : A -> Prop) (x : A) : (term642 A s x) = (s x).
Proof. exact (@lem4608919 (s x)). Qed.
Lemma lem4608921 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : s x.
Proof. exact (EQ_MP (@lem4608920 A s x) (@lem4608917 A s a t x h1)). Qed.
Lemma lem4608927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4608928 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : (term437 A s t _55361) = (term644 A t s _55361).
Proof. exact (@lem4608927 (t _55361) (term635 A s _55361)). Qed.
Lemma lem4608934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4608935 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : (term645 A s t _55361) = (term646 A t s _55361).
Proof. exact (MK_COMB (@lem4608934) (@lem4608928 A t s _55361)). Qed.
Lemma lem4608941 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : (term644 A t s _55361) = (term644 A t s _55361).
Proof. exact (eq_refl (term644 A t s _55361)). Qed.
Lemma lem4608942 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : ((term437 A s t _55361) = (term644 A t s _55361)) = ((term644 A t s _55361) = (term644 A t s _55361)).
Proof. exact (MK_COMB (@lem4608935 A t s _55361) (@lem4608941 A t s _55361)). Qed.
Lemma lem4608944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4608945 (x : Prop) : (x = x) = True.
Proof. exact (@lem4608944 Prop x). Qed.
Lemma lem4608946 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : ((term644 A t s _55361) = (term644 A t s _55361)) = True.
Proof. exact (@lem4608945 (term644 A t s _55361)). Qed.
Lemma lem4608947 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : ((term437 A s t _55361) = (term644 A t s _55361)) = True.
Proof. exact (TRANS (@lem4608942 A t s _55361) (@lem4608946 A t s _55361)). Qed.
Lemma lem4608948 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : True = ((term437 A s t _55361) = (term644 A t s _55361)).
Proof. exact (SYM (@lem4608947 A t s _55361)). Qed.
Lemma lem4608949 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55361 : A) : (term437 A s t _55361) = (term644 A t s _55361).
Proof. exact (EQ_MP (@lem4608948 A t s _55361) (@lem0)). Qed.
Lemma lem4608950 {A : Type'} (_55361 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term644 A t s _55361.
Proof. exact (EQ_MP (@lem4608949 A t s _55361) (@lem4608804 A _55361 s a t x h1)). Qed.
Lemma lem4608952 (b : Prop) (a : Prop) : (a \/ b) = (term647 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4608953 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55361 : A) : (term644 A t s _55361) = (term648 A s t _55361).
Proof. exact (@lem4608952 (term635 A s _55361) (t _55361)). Qed.
Lemma lem4608955 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4608956 {A : Type'} (s : A -> Prop) (_55361 : A) : (term649 A s _55361) = (s _55361).
Proof. exact (@lem4608955 (s _55361)). Qed.
Lemma lem4608957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4608958 {A : Type'} (s : A -> Prop) (_55361 : A) : (term650 A s _55361) = (term331 A s _55361).
Proof. exact (MK_COMB (@lem4608957) (@lem4608956 A s _55361)). Qed.
Lemma lem4608959 {A : Type'} (t : A -> Prop) (_55361 : A) : (t _55361) = (t _55361).
Proof. exact (eq_refl (t _55361)). Qed.
Lemma lem4608960 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55361 : A) : (term648 A s t _55361) = (term333 A s t _55361).
Proof. exact (MK_COMB (@lem4608958 A s _55361) (@lem4608959 A t _55361)). Qed.
Lemma lem4608961 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55361 : A) : (term644 A t s _55361) = (term333 A s t _55361).
Proof. exact (TRANS (@lem4608953 A s t _55361) (@lem4608960 A s t _55361)). Qed.
Lemma lem4608964 {A : Type'} (_55361 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term333 A s t _55361.
Proof. exact (EQ_MP (@lem4608961 A s t _55361) (@lem4608950 A _55361 s a t x h1)). Qed.
Lemma lem4608965 {A : Type'} (_55361 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term333 A s t _55361.
Proof. exact (@lem4608964 A _55361 s a t x h1). Qed.
Lemma lem4608966 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term333 A s t x.
Proof. exact (@lem4608965 A x s a t x h1). Qed.
Lemma lem4608969 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : t x.
Proof. exact (@lem4608966 A s a t x h1 (@lem4608921 A s a t x h1)). Qed.
Lemma lem4608970 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term642 A t x.
Proof. exact (fun h0 : term635 A t x => @lem4608969 A s a t x h1). Qed.
Lemma lem4608972 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4608973 {A : Type'} (t : A -> Prop) (x : A) : (term642 A t x) = (t x).
Proof. exact (@lem4608972 (t x)). Qed.
Lemma lem4608974 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : t x.
Proof. exact (EQ_MP (@lem4608973 A t x) (@lem4608970 A s a t x h1)). Qed.
Lemma lem4608977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4608979 {A : Type'} (t : A -> Prop) (x : A) : (term635 A t x) = (term651 A t x).
Proof. exact (@lem4608977 (t x)). Qed.
Lemma lem4608982 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term651 A t x.
Proof. exact (EQ_MP (@lem4608979 A t x) (@lem4608806 A s a t x h1)). Qed.
Lemma lem4608985 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : False.
Proof. exact (@lem4608982 A s a t x h1 (@lem4608974 A s a t x h1)). Qed.
Lemma lem4608986 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : term652.
Proof. exact (fun h0 : ~ False => @lem4608985 A s a t x h1). Qed.
Lemma lem4608988 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4608989 : term652 = False.
Proof. exact (@lem4608988 False). Qed.
Lemma lem4608990 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term522 A s a t x) : False.
Proof. exact (EQ_MP (@lem4608989) (@lem4608986 A s a t x h1)). Qed.
Lemma lem4609018 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4609019 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4609018 A x). Qed.
Lemma lem4609020 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4609019 A a). Qed.
Lemma lem4609021 {A : Type'} (a : A) : term653 A a.
Proof. exact (fun h0 : term639 A a => @lem4609020 A a). Qed.
Lemma lem4609023 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4609024 {A : Type'} (a : A) : (term653 A a) = (a = a).
Proof. exact (@lem4609023 (a = a)). Qed.
Lemma lem4609025 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4609024 A a) (@lem4609021 A a)). Qed.
Lemma lem4609028 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4609030 {A : Type'} (a : A) : (term639 A a) = (term654 A a).
Proof. exact (@lem4609028 (a = a)). Qed.
Lemma lem4609033 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : term654 A a.
Proof. exact (EQ_MP (@lem4609030 A a) (@lem4608888 A s t x a h1 h2)). Qed.
Lemma lem4609036 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : False.
Proof. exact (@lem4609033 A s t x a h1 h2 (@lem4609025 A a)). Qed.
Lemma lem4609037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : term652.
Proof. exact (fun h0 : ~ False => @lem4609036 A s t x a h1 h2). Qed.
Lemma lem4609039 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4609040 : term652 = False.
Proof. exact (@lem4609039 False). Qed.
Lemma lem4609069 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem4609070 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term642 A s x.
Proof. exact (fun h0 : term635 A s x => @lem4609069 A s x h1). Qed.
Lemma lem4609072 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4609073 {A : Type'} (s : A -> Prop) (x : A) : (term642 A s x) = (s x).
Proof. exact (@lem4609072 (s x)). Qed.
Lemma lem4609074 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem4609073 A s x) (@lem4609070 A s x h1)). Qed.
Lemma lem4609080 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4609081 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : (term437 A s t _55363) = (term644 A t s _55363).
Proof. exact (@lem4609080 (t _55363) (term635 A s _55363)). Qed.
Lemma lem4609087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4609088 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : (term645 A s t _55363) = (term646 A t s _55363).
Proof. exact (MK_COMB (@lem4609087) (@lem4609081 A t s _55363)). Qed.
Lemma lem4609094 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : (term644 A t s _55363) = (term644 A t s _55363).
Proof. exact (eq_refl (term644 A t s _55363)). Qed.
Lemma lem4609095 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : ((term437 A s t _55363) = (term644 A t s _55363)) = ((term644 A t s _55363) = (term644 A t s _55363)).
Proof. exact (MK_COMB (@lem4609088 A t s _55363) (@lem4609094 A t s _55363)). Qed.
Lemma lem4609097 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4609098 (x : Prop) : (x = x) = True.
Proof. exact (@lem4609097 Prop x). Qed.
Lemma lem4609099 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : ((term644 A t s _55363) = (term644 A t s _55363)) = True.
Proof. exact (@lem4609098 (term644 A t s _55363)). Qed.
Lemma lem4609100 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : ((term437 A s t _55363) = (term644 A t s _55363)) = True.
Proof. exact (TRANS (@lem4609095 A t s _55363) (@lem4609099 A t s _55363)). Qed.
Lemma lem4609101 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : True = ((term437 A s t _55363) = (term644 A t s _55363)).
Proof. exact (SYM (@lem4609100 A t s _55363)). Qed.
Lemma lem4609102 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55363 : A) : (term437 A s t _55363) = (term644 A t s _55363).
Proof. exact (EQ_MP (@lem4609101 A t s _55363) (@lem0)). Qed.
Lemma lem4609103 {A : Type'} (_55363 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term644 A t s _55363.
Proof. exact (EQ_MP (@lem4609102 A t s _55363) (@lem4608828 A _55363 s a t x h1)). Qed.
Lemma lem4609105 (b : Prop) (a : Prop) : (a \/ b) = (term647 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4609106 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55363 : A) : (term644 A t s _55363) = (term648 A s t _55363).
Proof. exact (@lem4609105 (term635 A s _55363) (t _55363)). Qed.
Lemma lem4609108 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4609109 {A : Type'} (s : A -> Prop) (_55363 : A) : (term649 A s _55363) = (s _55363).
Proof. exact (@lem4609108 (s _55363)). Qed.
Lemma lem4609110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609111 {A : Type'} (s : A -> Prop) (_55363 : A) : (term650 A s _55363) = (term331 A s _55363).
Proof. exact (MK_COMB (@lem4609110) (@lem4609109 A s _55363)). Qed.
Lemma lem4609112 {A : Type'} (t : A -> Prop) (_55363 : A) : (t _55363) = (t _55363).
Proof. exact (eq_refl (t _55363)). Qed.
Lemma lem4609113 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55363 : A) : (term648 A s t _55363) = (term333 A s t _55363).
Proof. exact (MK_COMB (@lem4609111 A s _55363) (@lem4609112 A t _55363)). Qed.
Lemma lem4609114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55363 : A) : (term644 A t s _55363) = (term333 A s t _55363).
Proof. exact (TRANS (@lem4609106 A s t _55363) (@lem4609113 A s t _55363)). Qed.
Lemma lem4609117 {A : Type'} (_55363 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term333 A s t _55363.
Proof. exact (EQ_MP (@lem4609114 A s t _55363) (@lem4609103 A _55363 s a t x h1)). Qed.
Lemma lem4609118 {A : Type'} (_55363 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term333 A s t _55363.
Proof. exact (@lem4609117 A _55363 s a t x h1). Qed.
Lemma lem4609119 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term333 A s t x.
Proof. exact (@lem4609118 A x s a t x h1). Qed.
Lemma lem4609122 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : t x.
Proof. exact (@lem4609119 A s a t x h2 (@lem4609074 A s x h1)). Qed.
Lemma lem4609123 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : term642 A t x.
Proof. exact (fun h0 : term635 A t x => @lem4609122 A s a t x h1 h2). Qed.
Lemma lem4609125 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4609126 {A : Type'} (t : A -> Prop) (x : A) : (term642 A t x) = (t x).
Proof. exact (@lem4609125 (t x)). Qed.
Lemma lem4609127 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : t x.
Proof. exact (EQ_MP (@lem4609126 A t x) (@lem4609123 A s a t x h1 h2)). Qed.
Lemma lem4609130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4609132 {A : Type'} (t : A -> Prop) (x : A) : (term635 A t x) = (term651 A t x).
Proof. exact (@lem4609130 (t x)). Qed.
Lemma lem4609135 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : term651 A t x.
Proof. exact (EQ_MP (@lem4609132 A t x) (@lem4608830 A s a t x h1)). Qed.
Lemma lem4609138 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : False.
Proof. exact (@lem4609135 A s a t x h2 (@lem4609127 A s a t x h1 h2)). Qed.
Lemma lem4609139 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : term652.
Proof. exact (fun h0 : ~ False => @lem4609138 A s a t x h1 h2). Qed.
Lemma lem4609141 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4609142 : term652 = False.
Proof. exact (@lem4609141 False). Qed.
Lemma lem4609143 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : False.
Proof. exact (EQ_MP (@lem4609142) (@lem4609139 A s a t x h1 h2)). Qed.
Lemma lem4609144 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4609040) (@lem4609037 A s t x a h1 h2)). Qed.
Lemma lem4609145 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4609143 A s a t x h1 h2) (fun h3 : False => @lem4608834 A s x h1)). Qed.
Lemma lem4609146 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : False.
Proof. exact (EQ_MP (@lem4609145 A s a t x h1 h2) (@lem4608834 A s x h1)). Qed.
Lemma lem4609147 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4609144 A s t x a h1 h2) (fun h3 : False => @lem4608822 A x a h2)). Qed.
Lemma lem4609148 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4609147 A s t x a h1 h2) (@lem4608822 A x a h2)). Qed.
Lemma lem4609149 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4609146 A s a t x h1 h2) (fun h3 : False => @lem4608789 A s x h1)). Qed.
Lemma lem4609150 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : False.
Proof. exact (EQ_MP (@lem4609149 A s a t x h1 h2) (@lem4608789 A s x h1)). Qed.
Lemma lem4609151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4609148 A s t x a h1 h2) (fun h3 : False => @lem4608764 A x a h2)). Qed.
Lemma lem4609152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4609151 A s t x a h1 h2) (@lem4608764 A x a h2)). Qed.
Lemma lem4609153 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem4609150 A s a t x h1 h2) (fun h3 : False => @lem4608789 A s x h1)). Qed.
Lemma lem4609154 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term541 A s a t x) : False.
Proof. exact (EQ_MP (@lem4609153 A s a t x h1 h2) (@lem4608789 A s x h1)). Qed.
Lemma lem4609155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4609152 A s t x a h1 h2) (fun h3 : False => @lem4608764 A x a h2)). Qed.
Lemma lem4609156 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (a : A) (h1 : term541 A s a t x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4609155 A s t x a h1 h2) (@lem4608764 A x a h2)). Qed.
Lemma lem4609157 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term541 A s a t x) : False.
Proof. exact (or_elim (@lem4608712 A s a t x h1) (fun h0 : x = a => @lem4609156 A s t x a h1 h0) (fun h0 : s x => @lem4609154 A s a t x h0 h1)). Qed.
Lemma lem4609158 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term624 A s a t x) : False.
Proof. exact (or_elim (@lem4608698 A s a t x h1) (fun h0 : term522 A s a t x => @lem4608990 A s a t x h0) (fun h0 : term541 A s a t x => @lem4609157 A s a t x h0)). Qed.
Lemma lem4609159 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term624 A s a t x) : (term624 A s a t x) = False.
Proof. exact (prop_ext (fun h2 : term624 A s a t x => @lem4609158 A s a t x h1) (fun h2 : False => @lem4608698 A s a t x h1)). Qed.
Lemma lem4609160 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term624 A s a t x) : False.
Proof. exact (EQ_MP (@lem4609159 A s a t x h1) (@lem4608698 A s a t x h1)). Qed.
Lemma lem4609161 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term627 A s a t) : False.
Proof. exact (ex_elim (@lem4608609 A s a t h1) (fun x : A => fun h0 : term626 A s a t x => @lem4609160 A s a t x h0)). Qed.
Lemma lem4609162 {A : Type'} (a : A) (t : A -> Prop) (h1 : term629 A a t) : False.
Proof. exact (ex_elim (@lem4608608 A a t h1) (fun s : A -> Prop => fun h0 : term628 A a t s => @lem4609161 A s a t h0)). Qed.
Lemma lem4609163 {A : Type'} (t : A -> Prop) (h1 : term631 A t) : False.
Proof. exact (ex_elim (@lem4608607 A t h1) (fun a : A => fun h0 : term630 A t a => @lem4609162 A a t h0)). Qed.
Lemma lem4609164 {A : Type'} (h1 : term436 A) : False.
Proof. exact (ex_elim (@lem4608606 A h1) (fun t : A -> Prop => fun h0 : term632 A t => @lem4609163 A t h0)). Qed.
Lemma lem4609165 {A : Type'} (h1 : term436 A) : (term436 A) = False.
Proof. exact (prop_ext (fun h2 : term436 A => @lem4609164 A h1) (fun h2 : False => @lem4608007 A h1)). Qed.
Lemma lem4609166 {A : Type'} (h1 : term436 A) : False.
Proof. exact (EQ_MP (@lem4609165 A h1) (@lem4608007 A h1)). Qed.
Lemma lem4609167 {A : Type'} : term435 A.
Proof. exact (fun h0 : term436 A => @lem4609166 A h0). Qed.
Lemma lem4609168 {A : Type'} : term434 A.
Proof. exact (EQ_MP (@lem4608006 A) (@lem4609167 A)). Qed.
Lemma lem4609169 {A : Type'} : term411 A.
Proof. exact (EQ_MP (@lem4608002 A) (@lem4609168 A)). Qed.
Lemma lem4609170 {A : Type'} (t : A -> Prop) : term655 A t.
Proof. exact (@lem4609169 A t). Qed.
Lemma lem4609171 {A : Type'} (t : A -> Prop) : (term655 A t) = (term385 A t).
Proof. exact (eq_refl (term655 A t)). Qed.
Lemma lem4609172 {A : Type'} (t : A -> Prop) : term385 A t.
Proof. exact (EQ_MP (@lem4609171 A t) (@lem4609170 A t)). Qed.
Lemma lem4609173 {A : Type'} (t : A -> Prop) (a : A) : term656 A t a.
Proof. exact (@lem4609172 A t a). Qed.
Lemma lem4609174 {A : Type'} (a : A) (t : A -> Prop) : (term656 A t a) = (term376 A a t).
Proof. exact (eq_refl (term656 A t a)). Qed.
Lemma lem4609175 {A : Type'} (a : A) (t : A -> Prop) : term376 A a t.
Proof. exact (EQ_MP (@lem4609174 A a t) (@lem4609173 A t a)). Qed.
Lemma lem4609177 {A : Type'} (a : A) (t : A -> Prop) : term376 A a t.
Proof. exact (@lem4607606 A a t (@lem4609175 A a t)). Qed.
Lemma lem4609178 {A : Type'} (a : A) (t : A -> Prop) (h1 : term377 A a t) : False.
Proof. exact (@lem4609177 A a t (@lem4607590 A a t h1)). Qed.
Lemma lem4609179 {A : Type'} (a : A) (t : A -> Prop) (h1 : term377 A a t) : (term377 A a t) = False.
Proof. exact (prop_ext (fun h2 : term377 A a t => @lem4609178 A a t h1) (fun h2 : False => @lem4607590 A a t h1)). Qed.
Lemma lem4609180 {A : Type'} (a : A) (t : A -> Prop) (h1 : term377 A a t) : False.
Proof. exact (EQ_MP (@lem4609179 A a t h1) (@lem4607590 A a t h1)). Qed.
Lemma lem4609181 {A : Type'} (a : A) (t : A -> Prop) : term376 A a t.
Proof. exact (fun h0 : term377 A a t => @lem4609180 A a t h0). Qed.
Lemma lem4609182 {A : Type'} (a : A) (t : A -> Prop) : term374 A a t.
Proof. exact (EQ_MP (@lem4607589 A a t) (@lem4609181 A a t)). Qed.
Lemma lem4609183 {A : Type'} (a : A) (t : A -> Prop) : term329 A a t.
Proof. exact (EQ_MP (@lem4607585 A a t) (@lem4609182 A a t)). Qed.
Lemma lem4609184 {A : Type'} (a : A) (t : A -> Prop) : term316 A a t.
Proof. exact (EQ_MP (@lem4607394 A a t) (@lem4609183 A a t)). Qed.
Lemma lem4609185 (t1 : Prop) : term657 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4609186 (t1 : Prop) : (term657 t1) = (term658 t1).
Proof. exact (eq_refl (term657 t1)). Qed.
Lemma lem4609187 (t1 : Prop) : term658 t1.
Proof. exact (EQ_MP (@lem4609186 t1) (@lem4609185 t1)). Qed.
Lemma lem4609188 (t1 : Prop) (t2 : Prop) : term659 t1 t2.
Proof. exact (@lem4609187 t1 t2). Qed.
Lemma lem4609189 (t1 : Prop) (t2 : Prop) : (term659 t1 t2) = (term660 t1 t2).
Proof. exact (eq_refl (term659 t1 t2)). Qed.
Lemma lem4609190 (t1 : Prop) (t2 : Prop) : term660 t1 t2.
Proof. exact (EQ_MP (@lem4609189 t1 t2) (@lem4609188 t1 t2)). Qed.
Lemma lem4609191 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term661 t1 t2 t3.
Proof. exact (@lem4609190 t1 t2 t3). Qed.
Lemma lem4609192 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term661 t1 t2 t3) = ((term662 t1 t2 t3) = (term663 t1 t2 t3)).
Proof. exact (eq_refl (term661 t1 t2 t3)). Qed.
Lemma lem4609193 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term662 t1 t2 t3) = (term663 t1 t2 t3).
Proof. exact (EQ_MP (@lem4609192 t1 t2 t3) (@lem4609191 t1 t2 t3)). Qed.
Lemma lem4609194 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term663 t1 t2 t3) = (term662 t1 t2 t3).
Proof. exact (SYM (@lem4609193 t1 t2 t3)). Qed.
Lemma lem4609200 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4609201 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4609200 A s t). Qed.
Lemma lem4609202 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term62 A s a t) = (term319 A s a t).
Proof. exact (@lem4609201 A (@DELETE A s a) t). Qed.
Lemma lem4609209 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609210 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term155 A s a t) = (term664 A s a t).
Proof. exact (MK_COMB (@lem4609209) (@lem4609202 A s a t)). Qed.
Lemma lem4609214 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4609215 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4609214 A s t). Qed.
Lemma lem4609222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4609223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term276 A s t) = (term665 A s t).
Proof. exact (MK_COMB (@lem4609222) (@lem4609215 A s t)). Qed.
Lemma lem4609233 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term666 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4609234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term666 A s t).
Proof. exact (@lem4609233 A s t). Qed.
Lemma lem4609235 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (s = (@INSERT A a x)) = (term667 A s a x).
Proof. exact (@lem4609234 A s (@INSERT A a x)). Qed.
Lemma lem4609244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4609245 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term285 A s a x) = (term668 A s a x).
Proof. exact (MK_COMB (@lem4609244) (@lem4609235 A s a x)). Qed.
Lemma lem4609247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4609248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4609247 A s t). Qed.
Lemma lem4609249 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (@SUBSET A x t) = (term36 A x t).
Proof. exact (@lem4609248 A x t). Qed.
Lemma lem4609256 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term287 A s a x t) = (term669 A s a x t).
Proof. exact (MK_COMB (@lem4609245 A s a x) (@lem4609249 A x t)). Qed.
Lemma lem4609259 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term289 A s a t) = (term670 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4609256 A s a x t)). Qed.
Lemma lem4609260 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4609261 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term290 A s a t) = (term671 A s a t).
Proof. exact (MK_COMB (@lem4609260 A) (@lem4609259 A s a t)). Qed.
Lemma lem4609266 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term291 A s a t) = (term672 A s a t).
Proof. exact (MK_COMB (@lem4609223 A s t) (@lem4609261 A s a t)). Qed.
Lemma lem4609269 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term292 A s a t) = (term673 A s a t).
Proof. exact (MK_COMB (@lem4609210 A s a t) (@lem4609266 A s a t)). Qed.
Lemma lem4609272 {A : Type'} (a : A) (s : A -> Prop) : (term674 A a s) = (term674 A a s).
Proof. exact (eq_refl (term674 A a s)). Qed.
Lemma lem4609273 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term675 A s a t) = (term676 A s a t).
Proof. exact (MK_COMB (@lem4609272 A a s) (@lem4609269 A s a t)). Qed.
Lemma lem4609276 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term676 A s a t) = (term675 A s a t).
Proof. exact (SYM (@lem4609273 A s a t)). Qed.
Lemma lem4609280 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609281 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609280 A P x). Qed.
Lemma lem4609282 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem4609281 A s a). Qed.
Lemma lem4609283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4609284 {A : Type'} (s : A -> Prop) (a : A) : (term2 A a s) = (term635 A s a).
Proof. exact (MK_COMB (@lem4609283) (@lem4609282 A s a)). Qed.
Lemma lem4609285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609286 {A : Type'} (s : A -> Prop) (a : A) : (term674 A a s) = (term677 A s a).
Proof. exact (MK_COMB (@lem4609285) (@lem4609284 A s a)). Qed.
Lemma lem4609296 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4609297 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4609296 A s x y). Qed.
Lemma lem4609298 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term339 A s x a).
Proof. exact (@lem4609297 A s x a). Qed.
Lemma lem4609302 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609303 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609302 A P x). Qed.
Lemma lem4609304 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4609303 A s x). Qed.
Lemma lem4609305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4609306 {A : Type'} (s : A -> Prop) (x : A) : (term340 A x s) = (term341 A s x).
Proof. exact (MK_COMB (@lem4609305) (@lem4609304 A s x)). Qed.
Lemma lem4609309 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4609310 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term339 A s x a) = (term343 A s x a).
Proof. exact (MK_COMB (@lem4609306 A s x) (@lem4609309 A x a)). Qed.
Lemma lem4609313 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term343 A s x a).
Proof. exact (TRANS (@lem4609298 A s x a) (@lem4609310 A s x a)). Qed.
Lemma lem4609314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609315 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term344 A x s a) = (term345 A s x a).
Proof. exact (MK_COMB (@lem4609314) (@lem4609313 A s x a)). Qed.
Lemma lem4609317 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609317 A P x). Qed.
Lemma lem4609319 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4609318 A t x). Qed.
Lemma lem4609320 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term346 A s a x t) = (term347 A s a t x).
Proof. exact (MK_COMB (@lem4609315 A s x a) (@lem4609319 A t x)). Qed.
Lemma lem4609323 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term348 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4609320 A s a t x)). Qed.
Lemma lem4609324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609325 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term319 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4609324 A) (@lem4609323 A s a t)). Qed.
Lemma lem4609330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609331 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term664 A s a t) = (term678 A s a t).
Proof. exact (MK_COMB (@lem4609330) (@lem4609325 A s a t)). Qed.
Lemma lem4609341 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609342 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609341 A P x). Qed.
Lemma lem4609343 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4609342 A s x). Qed.
Lemma lem4609344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609345 {A : Type'} (s : A -> Prop) (x : A) : (term330 A x s) = (term331 A s x).
Proof. exact (MK_COMB (@lem4609344) (@lem4609343 A s x)). Qed.
Lemma lem4609347 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609348 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609347 A P x). Qed.
Lemma lem4609349 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4609348 A t x). Qed.
Lemma lem4609350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term332 A s x t) = (term333 A s t x).
Proof. exact (MK_COMB (@lem4609345 A s x) (@lem4609349 A t x)). Qed.
Lemma lem4609353 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term334 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4609350 A s t x)). Qed.
Lemma lem4609354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4609354 A) (@lem4609353 A s t)). Qed.
Lemma lem4609360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4609361 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term665 A s t) = (term679 A s t).
Proof. exact (MK_COMB (@lem4609360) (@lem4609355 A s t)). Qed.
Lemma lem4609375 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609376 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609375 A P x). Qed.
Lemma lem4609377 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4609376 A s x). Qed.
Lemma lem4609378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4609379 {A : Type'} (s : A -> Prop) (x : A) : (term680 A x s) = (term681 A s x).
Proof. exact (MK_COMB (@lem4609378) (@lem4609377 A s x)). Qed.
Lemma lem4609381 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4609382 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (@lem4609381 A y x s). Qed.
Lemma lem4609383 {A : Type'} (a : A) (x : A) (x' : A -> Prop) : (term357 A x a x') = (term358 A a x x').
Proof. exact (@lem4609382 A a x x'). Qed.
Lemma lem4609389 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609390 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609389 A P x). Qed.
Lemma lem4609391 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4609390 A x x'). Qed.
Lemma lem4609392 {A : Type'} (x : A) (a : A) : (term359 A x a) = (term359 A x a).
Proof. exact (eq_refl (term359 A x a)). Qed.
Lemma lem4609393 {A : Type'} (a : A) (x : A -> Prop) (x' : A) : (term358 A a x' x) = (term360 A a x x').
Proof. exact (MK_COMB (@lem4609392 A x' a) (@lem4609391 A x x')). Qed.
Lemma lem4609396 {A : Type'} (a : A) (x : A -> Prop) (x' : A) : (term357 A x' a x) = (term360 A a x x').
Proof. exact (TRANS (@lem4609383 A a x' x) (@lem4609393 A a x x')). Qed.
Lemma lem4609397 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : ((@IN A x' s) = (term357 A x' a x)) = ((s x') = (term360 A a x x')).
Proof. exact (MK_COMB (@lem4609379 A s x') (@lem4609396 A a x x')). Qed.
Lemma lem4609400 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term682 A s a x) = (term683 A s a x).
Proof. exact (fun_ext (fun x' : A => @lem4609397 A s a x x')). Qed.
Lemma lem4609401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609402 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term667 A s a x) = (term684 A s a x).
Proof. exact (MK_COMB (@lem4609401 A) (@lem4609400 A s a x)). Qed.
Lemma lem4609407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4609408 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term668 A s a x) = (term685 A s a x).
Proof. exact (MK_COMB (@lem4609407) (@lem4609402 A s a x)). Qed.
Lemma lem4609416 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609417 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609416 A P x). Qed.
Lemma lem4609418 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem4609417 A x x'). Qed.
Lemma lem4609419 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609420 {A : Type'} (x : A -> Prop) (x' : A) : (term330 A x' x) = (term331 A x x').
Proof. exact (MK_COMB (@lem4609419) (@lem4609418 A x x')). Qed.
Lemma lem4609422 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4609423 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4609422 A P x). Qed.
Lemma lem4609424 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4609423 A t x). Qed.
Lemma lem4609425 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term332 A x x' t) = (term333 A x t x').
Proof. exact (MK_COMB (@lem4609420 A x x') (@lem4609424 A t x')). Qed.
Lemma lem4609428 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term334 A x t) = (term335 A x t).
Proof. exact (fun_ext (fun x' : A => @lem4609425 A x t x')). Qed.
Lemma lem4609429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609430 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term36 A x t) = (term336 A x t).
Proof. exact (MK_COMB (@lem4609429 A) (@lem4609428 A x t)). Qed.
Lemma lem4609435 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term669 A s a x t) = (term686 A s a x t).
Proof. exact (MK_COMB (@lem4609408 A s a x) (@lem4609430 A x t)). Qed.
Lemma lem4609438 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term670 A s a t) = (term687 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4609435 A s a x t)). Qed.
Lemma lem4609439 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4609440 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term671 A s a t) = (term688 A s a t).
Proof. exact (MK_COMB (@lem4609439 A) (@lem4609438 A s a t)). Qed.
Lemma lem4609445 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term672 A s a t) = (term689 A s a t).
Proof. exact (MK_COMB (@lem4609361 A s t) (@lem4609440 A s a t)). Qed.
Lemma lem4609448 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term673 A s a t) = (term690 A s a t).
Proof. exact (MK_COMB (@lem4609331 A s a t) (@lem4609445 A s a t)). Qed.
Lemma lem4609451 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term676 A s a t) = (term691 A s a t).
Proof. exact (MK_COMB (@lem4609286 A s a) (@lem4609448 A s a t)). Qed.
Lemma lem4609454 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term691 A s a t) = (term676 A s a t).
Proof. exact (SYM (@lem4609451 A s a t)). Qed.
Lemma lem4609456 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4609457 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term691 A s a t) = (term692 A s a t).
Proof. exact (@lem4609456 (term691 A s a t)). Qed.
Lemma lem4609458 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term692 A s a t) = (term691 A s a t).
Proof. exact (SYM (@lem4609457 A s a t)). Qed.
Lemma lem4609459 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term693 A s a t) : term693 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609462 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term692 A s a t) : term692 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609463 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term694 A s a t.
Proof. exact (fun h0 : term692 A s a t => @lem4609462 A s a t h0). Qed.
Lemma lem4609464 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term694 A s a t) : term694 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609465 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term692 A s a t) : term692 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609466 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term692 A s a t) (h2 : term694 A s a t) : term692 A s a t.
Proof. exact (@lem4609464 A s a t h2 (@lem4609465 A s a t h1)). Qed.
Lemma lem4609467 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term692 A s a t) : term695 A s a t.
Proof. exact (fun h0 : term694 A s a t => @lem4609466 A s a t h1 h0). Qed.
Lemma lem4609468 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term694 A s a t) : term694 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609469 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term692 A s a t) (h2 : term694 A s a t) : term692 A s a t.
Proof. exact (@lem4609467 A s a t h1 (@lem4609468 A s a t h2)). Qed.
Lemma lem4609470 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term694 A s a t) : term694 A s a t.
Proof. exact (fun h0 : term692 A s a t => @lem4609469 A s a t h0 h1). Qed.
Lemma lem4609471 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term696 A s a t.
Proof. exact (fun h0 : term694 A s a t => @lem4609470 A s a t h0). Qed.
Lemma lem4609474 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term694 A s a t.
Proof. exact (@lem4609471 A s a t (@lem4609463 A s a t)). Qed.
Lemma lem4609475 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term694 A s a t.
Proof. exact (@lem4609474 A s a t). Qed.
Lemma lem4609489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4609490 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term692 A s a t) = (term697 A s a t).
Proof. exact (@lem4609489 (term693 A s a t)). Qed.
Lemma lem4609492 (t : Prop) : (term382 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4609493 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term697 A s a t) = (term691 A s a t).
Proof. exact (@lem4609492 (term691 A s a t)). Qed.
Lemma lem4609496 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term692 A s a t) = (term691 A s a t).
Proof. exact (TRANS (@lem4609490 A s a t) (@lem4609493 A s a t)). Qed.
Lemma lem4609577 {A : Type'} (a : A) (t : A -> Prop) : (term698 A a t) = (term699 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4609496 A s a t)). Qed.
Lemma lem4609578 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4609579 {A : Type'} (a : A) (t : A -> Prop) : (term700 A a t) = (term701 A a t).
Proof. exact (MK_COMB (@lem4609578 A) (@lem4609577 A a t)). Qed.
Lemma lem4609584 {A : Type'} (t : A -> Prop) : (term702 A t) = (term703 A t).
Proof. exact (fun_ext (fun a : A => @lem4609579 A a t)). Qed.
Lemma lem4609585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609586 {A : Type'} (t : A -> Prop) : (term704 A t) = (term705 A t).
Proof. exact (MK_COMB (@lem4609585 A) (@lem4609584 A t)). Qed.
Lemma lem4609591 {A : Type'} : (term706 A) = (term707 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4609586 A t)). Qed.
Lemma lem4609592 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4609601 {A : Type'} : (term708 A) = (term709 A).
Proof. exact (MK_COMB (@lem4609592 A) (@lem4609591 A)). Qed.
Lemma lem4609606 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term333 A x t x') = (term333 A x t x').
Proof. exact (eq_refl (term333 A x t x')). Qed.
Lemma lem4609607 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term335 A x t) = (term335 A x t).
Proof. exact (fun_ext (fun x' : A => @lem4609606 A x t x')). Qed.
Lemma lem4609608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609609 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term336 A x t) = (term336 A x t).
Proof. exact (MK_COMB (@lem4609608 A) (@lem4609607 A x t)). Qed.
Lemma lem4609618 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : ((s x') = (term360 A a x x')) = ((s x') = (term360 A a x x')).
Proof. exact (eq_refl ((s x') = (term360 A a x x'))). Qed.
Lemma lem4609619 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term683 A s a x) = (term683 A s a x).
Proof. exact (fun_ext (fun x' : A => @lem4609618 A s a x x')). Qed.
Lemma lem4609620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609621 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term684 A s a x) = (term684 A s a x).
Proof. exact (MK_COMB (@lem4609620 A) (@lem4609619 A s a x)). Qed.
Lemma lem4609622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4609623 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term685 A s a x) = (term685 A s a x).
Proof. exact (MK_COMB (@lem4609622) (@lem4609621 A s a x)). Qed.
Lemma lem4609624 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term686 A s a x t) = (term686 A s a x t).
Proof. exact (MK_COMB (@lem4609623 A s a x) (@lem4609609 A x t)). Qed.
Lemma lem4609625 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term687 A s a t) = (term687 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4609624 A s a x t)). Qed.
Lemma lem4609626 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4609627 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term688 A s a t) = (term688 A s a t).
Proof. exact (MK_COMB (@lem4609626 A) (@lem4609625 A s a t)). Qed.
Lemma lem4609632 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term333 A s t x) = (term333 A s t x).
Proof. exact (eq_refl (term333 A s t x)). Qed.
Lemma lem4609633 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term335 A s t) = (term335 A s t).
Proof. exact (fun_ext (fun x : A => @lem4609632 A s t x)). Qed.
Lemma lem4609634 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term336 A s t) = (term336 A s t).
Proof. exact (MK_COMB (@lem4609634 A) (@lem4609633 A s t)). Qed.
Lemma lem4609636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4609637 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term679 A s t) = (term679 A s t).
Proof. exact (MK_COMB (@lem4609636) (@lem4609635 A s t)). Qed.
Lemma lem4609638 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term689 A s a t) = (term689 A s a t).
Proof. exact (MK_COMB (@lem4609637 A s t) (@lem4609627 A s a t)). Qed.
Lemma lem4609649 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term347 A s a t x)). Qed.
Lemma lem4609650 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4609649 A s a t x)). Qed.
Lemma lem4609651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609652 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4609651 A) (@lem4609650 A s a t)). Qed.
Lemma lem4609653 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4609654 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term678 A s a t) = (term678 A s a t).
Proof. exact (MK_COMB (@lem4609653) (@lem4609652 A s a t)). Qed.
Lemma lem4609655 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term690 A s a t) = (term690 A s a t).
Proof. exact (MK_COMB (@lem4609654 A s a t) (@lem4609638 A s a t)). Qed.
Lemma lem4609660 {A : Type'} (s : A -> Prop) (a : A) : (term677 A s a) = (term677 A s a).
Proof. exact (eq_refl (term677 A s a)). Qed.
Lemma lem4609661 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term691 A s a t) = (term691 A s a t).
Proof. exact (MK_COMB (@lem4609660 A s a) (@lem4609655 A s a t)). Qed.
Lemma lem4609662 {A : Type'} (a : A) (t : A -> Prop) : (term699 A a t) = (term699 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4609661 A s a t)). Qed.
Lemma lem4609663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4609664 {A : Type'} (a : A) (t : A -> Prop) : (term701 A a t) = (term701 A a t).
Proof. exact (MK_COMB (@lem4609663 A) (@lem4609662 A a t)). Qed.
Lemma lem4609665 {A : Type'} (t : A -> Prop) : (term703 A t) = (term703 A t).
Proof. exact (fun_ext (fun a : A => @lem4609664 A a t)). Qed.
Lemma lem4609666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609667 {A : Type'} (t : A -> Prop) : (term705 A t) = (term705 A t).
Proof. exact (MK_COMB (@lem4609666 A) (@lem4609665 A t)). Qed.
Lemma lem4609668 {A : Type'} : (term707 A) = (term707 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4609667 A t)). Qed.
Lemma lem4609669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4609670 {A : Type'} : (term709 A) = (term709 A).
Proof. exact (MK_COMB (@lem4609669 A) (@lem4609668 A)). Qed.
Lemma lem4609739 {A : Type'} : (term708 A) = (term709 A).
Proof. exact (TRANS (@lem4609601 A) (@lem4609670 A)). Qed.
Lemma lem4609740 {A : Type'} : (term709 A) = (term708 A).
Proof. exact (SYM (@lem4609739 A)). Qed.
Lemma lem4609742 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term350 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609744 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4609745 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term689 A s a t) = (term710 A s a t).
Proof. exact (@lem4609744 (term689 A s a t)). Qed.
Lemma lem4609746 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term710 A s a t) = (term689 A s a t).
Proof. exact (SYM (@lem4609745 A s a t)). Qed.
Lemma lem4609747 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term711 A s a t) : term711 A s a t.
Proof. exact (h1). Qed.
Lemma lem4609753 {A : Type'} (s : A -> Prop) (a : A) (h1 : term635 A s a) : term635 A s a.
Proof. exact (h1). Qed.
Lemma lem4609757 {A : Type'} (x : A) (a : A) : (term712 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem4609759 {A : Type'} (s : A -> Prop) (x : A) : (term713 A s x) = (term713 A s x).
Proof. exact (eq_refl (term713 A s x)). Qed.
Lemma lem4609760 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term714 A s x a) = (term715 A s x a).
Proof. exact (MK_COMB (@lem4609759 A s x) (@lem4609757 A x a)). Qed.
Lemma lem4609761 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term714 A s x a).
Proof. exact (@lem17045 (s x) (term342 A x a)). Qed.
Lemma lem4609762 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term715 A s x a).
Proof. exact (TRANS (@lem4609761 A s x a) (@lem4609760 A s x a)). Qed.
Lemma lem4609763 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4609764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4609765 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term717 A s x a) = (term718 A s x a).
Proof. exact (MK_COMB (@lem4609764) (@lem4609762 A s x a)). Qed.
Lemma lem4609766 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term719 A s a t x) = (term720 A s a t x).
Proof. exact (MK_COMB (@lem4609765 A s x a) (@lem4609763 A t x)). Qed.
Lemma lem4609767 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term719 A s a t x).
Proof. exact (@lem17265 (term343 A s x a) (t x)). Qed.
Lemma lem4609768 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term720 A s a t x).
Proof. exact (TRANS (@lem4609767 A s a t x) (@lem4609766 A s a t x)). Qed.
Lemma lem4609769 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term721 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4609768 A s a t x)). Qed.
Lemma lem4609770 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4609807 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term722 A s a t).
Proof. exact (MK_COMB (@lem4609770 A) (@lem4609769 A s a t)). Qed.
Lemma lem4609808 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term722 A s a t.
Proof. exact (EQ_MP (@lem4609807 A s a t) (@lem4609742 A s a t h1)). Qed.
Lemma lem4609815 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term723 A s t x) = (term724 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem4609816 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4609817 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term725 A s t) = (term726 A s t).
Proof. exact (@lem4609816 A (term335 A s t)). Qed.
Lemma lem4609818 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term727 A s t x) = (term333 A s t x).
Proof. exact (eq_refl (term727 A s t x)). Qed.
Lemma lem4609819 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4609820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term728 A s t x) = (term723 A s t x).
Proof. exact (MK_COMB (@lem4609819) (@lem4609818 A s t x)). Qed.
Lemma lem4609821 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term728 A s t x) = (term724 A s t x).
Proof. exact (TRANS (@lem4609820 A s t x) (@lem4609815 A s t x)). Qed.
Lemma lem4609822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term729 A s t) = (term730 A s t).
Proof. exact (fun_ext (fun x : A => @lem4609821 A s t x)). Qed.
Lemma lem4609823 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4609824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term726 A s t) = (term731 A s t).
Proof. exact (MK_COMB (@lem4609823 A) (@lem4609822 A s t)). Qed.
Lemma lem4609825 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term725 A s t) = (term731 A s t).
Proof. exact (TRANS (@lem4609817 A s t) (@lem4609824 A s t)). Qed.
Lemma lem4609836 {A : Type'} (a : A) (x : A -> Prop) (x' : A) : (term732 A a x x') = (term733 A a x x').
Proof. exact (@lem17160 (x' = a) (x x')). Qed.
Lemma lem4609841 {A : Type'} (s : A -> Prop) (x : A) : (term713 A s x) = (term713 A s x).
Proof. exact (eq_refl (term713 A s x)). Qed.
Lemma lem4609842 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term734 A s a x x') = (term735 A s a x x').
Proof. exact (MK_COMB (@lem4609841 A s x') (@lem4609836 A a x x')). Qed.
Lemma lem4609847 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term736 A s a x x') = (term736 A s a x x').
Proof. exact (eq_refl (term736 A s a x x')). Qed.
Lemma lem4609848 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term737 A s a x x') = (term738 A s a x x').
Proof. exact (MK_COMB (@lem4609847 A s a x x') (@lem4609842 A s a x x')). Qed.
Lemma lem4609849 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term739 A s a x x') = (term737 A s a x x').
Proof. exact (@lem17930 (s x') (term360 A a x x')). Qed.
Lemma lem4609850 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term739 A s a x x') = (term738 A s a x x').
Proof. exact (TRANS (@lem4609849 A s a x x') (@lem4609848 A s a x x')). Qed.
Lemma lem4609851 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4609852 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term740 A s a x) = (term741 A s a x).
Proof. exact (@lem4609851 A (term683 A s a x)). Qed.
Lemma lem4609853 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term742 A s a x x') = ((s x') = (term360 A a x x')).
Proof. exact (eq_refl (term742 A s a x x')). Qed.
Lemma lem4609854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4609855 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term743 A s a x x') = (term739 A s a x x').
Proof. exact (MK_COMB (@lem4609854) (@lem4609853 A s a x x')). Qed.
Lemma lem4609856 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term743 A s a x x') = (term738 A s a x x').
Proof. exact (TRANS (@lem4609855 A s a x x') (@lem4609850 A s a x x')). Qed.
Lemma lem4609857 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term744 A s a x) = (term745 A s a x).
Proof. exact (fun_ext (fun x' : A => @lem4609856 A s a x x')). Qed.
Lemma lem4609858 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4609859 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term741 A s a x) = (term746 A s a x).
Proof. exact (MK_COMB (@lem4609858 A) (@lem4609857 A s a x)). Qed.
Lemma lem4609860 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term740 A s a x) = (term746 A s a x).
Proof. exact (TRANS (@lem4609852 A s a x) (@lem4609859 A s a x)). Qed.
Lemma lem4609867 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term723 A x t x') = (term724 A x t x').
Proof. exact (@lem17362 (x x') (t x')). Qed.
Lemma lem4609868 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4609869 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term725 A x t) = (term726 A x t).
Proof. exact (@lem4609868 A (term335 A x t)). Qed.
Lemma lem4609870 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term727 A x t x') = (term333 A x t x').
Proof. exact (eq_refl (term727 A x t x')). Qed.
Lemma lem4609871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4609872 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term728 A x t x') = (term723 A x t x').
Proof. exact (MK_COMB (@lem4609871) (@lem4609870 A x t x')). Qed.
Lemma lem4609873 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term728 A x t x') = (term724 A x t x').
Proof. exact (TRANS (@lem4609872 A x t x') (@lem4609867 A x t x')). Qed.
Lemma lem4609874 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term729 A x t) = (term730 A x t).
Proof. exact (fun_ext (fun x' : A => @lem4609873 A x t x')). Qed.
Lemma lem4609875 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4609876 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term726 A x t) = (term731 A x t).
Proof. exact (MK_COMB (@lem4609875 A) (@lem4609874 A x t)). Qed.
Lemma lem4609877 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term725 A x t) = (term731 A x t).
Proof. exact (TRANS (@lem4609869 A x t) (@lem4609876 A x t)). Qed.
Lemma lem4609878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4609879 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term747 A s a x) = (term748 A s a x).
Proof. exact (MK_COMB (@lem4609878) (@lem4609860 A s a x)). Qed.
Lemma lem4609880 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term749 A s a x t) = (term750 A s a x t).
Proof. exact (MK_COMB (@lem4609879 A s a x) (@lem4609877 A x t)). Qed.
Lemma lem4609881 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term751 A s a x t) = (term749 A s a x t).
Proof. exact (@lem17045 (term684 A s a x) (term336 A x t)). Qed.
Lemma lem4609882 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term751 A s a x t) = (term750 A s a x t).
Proof. exact (TRANS (@lem4609881 A s a x t) (@lem4609880 A s a x t)). Qed.
Lemma lem4609883 {A : Type'} (P : type686 A) : (term752 A P) = (term753 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4609884 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term754 A s a t) = (term755 A s a t).
Proof. exact (@lem4609883 A (term687 A s a t)). Qed.
Lemma lem4609885 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term756 A s a t x) = (term686 A s a x t).
Proof. exact (eq_refl (term756 A s a t x)). Qed.
Lemma lem4609886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4609887 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term757 A s a t x) = (term751 A s a x t).
Proof. exact (MK_COMB (@lem4609886) (@lem4609885 A s a x t)). Qed.
Lemma lem4609888 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term757 A s a t x) = (term750 A s a x t).
Proof. exact (TRANS (@lem4609887 A s a x t) (@lem4609882 A s a x t)). Qed.
Lemma lem4609889 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term758 A s a t) = (term759 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4609888 A s a x t)). Qed.
Lemma lem4609890 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4609891 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term755 A s a t) = (term760 A s a t).
Proof. exact (MK_COMB (@lem4609890 A) (@lem4609889 A s a t)). Qed.
Lemma lem4609892 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term754 A s a t) = (term760 A s a t).
Proof. exact (TRANS (@lem4609884 A s a t) (@lem4609891 A s a t)). Qed.
Lemma lem4609893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4609894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term761 A s t) = (term762 A s t).
Proof. exact (MK_COMB (@lem4609893) (@lem4609825 A s t)). Qed.
Lemma lem4609895 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term763 A s a t) = (term764 A s a t).
Proof. exact (MK_COMB (@lem4609894 A s t) (@lem4609892 A s a t)). Qed.
Lemma lem4609896 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term711 A s a t) = (term763 A s a t).
Proof. exact (@lem17160 (term336 A s t) (term688 A s a t)). Qed.
Lemma lem4609897 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term711 A s a t) = (term764 A s a t).
Proof. exact (TRANS (@lem4609896 A s a t) (@lem4609895 A s a t)). Qed.
Lemma lem4610052 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4610053 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (@lem4610052 A P Q). Qed.
Lemma lem4610054 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term765 A s a x t) = (term766 A s a x t).
Proof. exact (@lem4610053 A (term745 A s a x) (term730 A x t)). Qed.
Lemma lem4610055 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term767 A s a x x') = (term738 A s a x x').
Proof. exact (eq_refl (term767 A s a x x')). Qed.
Lemma lem4610056 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term768 A s a x) = (term745 A s a x).
Proof. exact (fun_ext (fun x' : A => @lem4610055 A s a x x')). Qed.
Lemma lem4610057 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610058 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term769 A s a x) = (term746 A s a x).
Proof. exact (MK_COMB (@lem4610057 A) (@lem4610056 A s a x)). Qed.
Lemma lem4610059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610060 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) : (term770 A s a x) = (term748 A s a x).
Proof. exact (MK_COMB (@lem4610059) (@lem4610058 A s a x)). Qed.
Lemma lem4610061 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term771 A x t x') = (term724 A x t x').
Proof. exact (eq_refl (term771 A x t x')). Qed.
Lemma lem4610062 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term772 A x t) = (term730 A x t).
Proof. exact (fun_ext (fun x' : A => @lem4610061 A x t x')). Qed.
Lemma lem4610063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610064 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term773 A x t) = (term731 A x t).
Proof. exact (MK_COMB (@lem4610063 A) (@lem4610062 A x t)). Qed.
Lemma lem4610065 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term765 A s a x t) = (term750 A s a x t).
Proof. exact (MK_COMB (@lem4610060 A s a x) (@lem4610064 A x t)). Qed.
Lemma lem4610066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4610067 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term774 A s a x t) = (term775 A s a x t).
Proof. exact (MK_COMB (@lem4610066) (@lem4610065 A s a x t)). Qed.
Lemma lem4610068 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term767 A s a x x') = (term738 A s a x x').
Proof. exact (eq_refl (term767 A s a x x')). Qed.
Lemma lem4610069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610070 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (x' : A) : (term776 A s a x x') = (term777 A s a x x').
Proof. exact (MK_COMB (@lem4610069) (@lem4610068 A s a x x')). Qed.
Lemma lem4610071 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term771 A x t x') = (term724 A x t x').
Proof. exact (eq_refl (term771 A x t x')). Qed.
Lemma lem4610072 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) (x' : A) : (term778 A s a x t x') = (term779 A s a x t x').
Proof. exact (MK_COMB (@lem4610070 A s a x x') (@lem4610071 A x t x')). Qed.
Lemma lem4610073 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term780 A s a x t) = (term781 A s a x t).
Proof. exact (fun_ext (fun x' : A => @lem4610072 A s a x t x')). Qed.
Lemma lem4610074 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610075 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term766 A s a x t) = (term782 A s a x t).
Proof. exact (MK_COMB (@lem4610074 A) (@lem4610073 A s a x t)). Qed.
Lemma lem4610076 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : ((term765 A s a x t) = (term766 A s a x t)) = ((term750 A s a x t) = (term782 A s a x t)).
Proof. exact (MK_COMB (@lem4610067 A s a x t) (@lem4610075 A s a x t)). Qed.
Lemma lem4610077 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term750 A s a x t) = (term782 A s a x t).
Proof. exact (EQ_MP (@lem4610076 A s a x t) (@lem4610054 A s a x t)). Qed.
Lemma lem4610078 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term759 A s a t) = (term783 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4610077 A s a x t)). Qed.
Lemma lem4610079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4610080 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term760 A s a t) = (term784 A s a t).
Proof. exact (MK_COMB (@lem4610079 A) (@lem4610078 A s a t)). Qed.
Lemma lem4610082 {A B : Type'} (P : type1413 A B) : (term785 A B P) = (term786 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4610083 {A : Type'} (P : type672 A) : (term787 A P) = (term788 A P).
Proof. exact (@lem4610082 (A -> Prop) A P). Qed.
Lemma lem4610084 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term789 A s a t) = (term790 A s a t).
Proof. exact (@lem4610083 A (term791 A s a t)). Qed.
Lemma lem4610085 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term792 A s a t x) = (term781 A s a x t).
Proof. exact (eq_refl (term792 A s a t x)). Qed.
Lemma lem4610086 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4610087 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) (x' : A) : (term793 A s a t x x') = (term794 A s a x t x').
Proof. exact (MK_COMB (@lem4610085 A s a x t) (@lem4610086 A x')). Qed.
Lemma lem4610088 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) (x' : A) : (term794 A s a x t x') = (term779 A s a x t x').
Proof. exact (eq_refl (term794 A s a x t x')). Qed.
Lemma lem4610089 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) (x' : A) : (term793 A s a t x x') = (term779 A s a x t x').
Proof. exact (TRANS (@lem4610087 A s a x t x') (@lem4610088 A s a x t x')). Qed.
Lemma lem4610090 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term795 A s a t x) = (term781 A s a x t).
Proof. exact (fun_ext (fun x' : A => @lem4610089 A s a x t x')). Qed.
Lemma lem4610091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610092 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term796 A s a t x) = (term782 A s a x t).
Proof. exact (MK_COMB (@lem4610091 A) (@lem4610090 A s a x t)). Qed.
Lemma lem4610093 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term797 A s a t) = (term783 A s a t).
Proof. exact (fun_ext (fun x : A -> Prop => @lem4610092 A s a x t)). Qed.
Lemma lem4610094 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4610095 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term789 A s a t) = (term784 A s a t).
Proof. exact (MK_COMB (@lem4610094 A) (@lem4610093 A s a t)). Qed.
Lemma lem4610096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4610097 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term798 A s a t) = (term799 A s a t).
Proof. exact (MK_COMB (@lem4610096) (@lem4610095 A s a t)). Qed.
Lemma lem4610098 {A : Type'} (s : A -> Prop) (a : A) (x : A -> Prop) (t : A -> Prop) : (term792 A s a t x) = (term781 A s a x t).
Proof. exact (eq_refl (term792 A s a t x)). Qed.
Lemma lem4610099 {A : Type'} (x : type684 A) (x' : A -> Prop) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4610100 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term800 A s a t x x') = (term801 A s a t x x').
Proof. exact (MK_COMB (@lem4610098 A s a x' t) (@lem4610099 A x x')). Qed.
Lemma lem4610101 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term801 A s a t x x') = (term802 A s a t x x').
Proof. exact (eq_refl (term801 A s a t x x')). Qed.
Lemma lem4610102 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) (x' : A -> Prop) : (term800 A s a t x x') = (term802 A s a t x x').
Proof. exact (TRANS (@lem4610100 A s a t x x') (@lem4610101 A s a t x x')). Qed.
Lemma lem4610103 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) : (term803 A s a t x) = (term804 A s a t x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4610102 A s a t x x')). Qed.
Lemma lem4610104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4610105 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) : (term805 A s a t x) = (term806 A s a t x).
Proof. exact (MK_COMB (@lem4610104 A) (@lem4610103 A s a t x)). Qed.
Lemma lem4610106 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term807 A s a t) = (term808 A s a t).
Proof. exact (fun_ext (fun x : type684 A => @lem4610105 A s a t x)). Qed.
Lemma lem4610107 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4610108 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term790 A s a t) = (term809 A s a t).
Proof. exact (MK_COMB (@lem4610107 A) (@lem4610106 A s a t)). Qed.
Lemma lem4610109 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term789 A s a t) = (term790 A s a t)) = ((term784 A s a t) = (term809 A s a t)).
Proof. exact (MK_COMB (@lem4610097 A s a t) (@lem4610108 A s a t)). Qed.
Lemma lem4610110 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term784 A s a t) = (term809 A s a t).
Proof. exact (EQ_MP (@lem4610109 A s a t) (@lem4610084 A s a t)). Qed.
Lemma lem4610111 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term760 A s a t) = (term809 A s a t).
Proof. exact (TRANS (@lem4610080 A s a t) (@lem4610110 A s a t)). Qed.
Lemma lem4610112 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term762 A s t) = (term762 A s t).
Proof. exact (eq_refl (term762 A s t)). Qed.
Lemma lem4610113 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term764 A s a t) = (term810 A s a t).
Proof. exact (MK_COMB (@lem4610112 A s t) (@lem4610111 A s a t)). Qed.
Lemma lem4610115 {A : Type'} (P : A -> Prop) (Q : Prop) : (term811 A P Q) = (term812 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4610116 {A : Type'} (P : A -> Prop) (Q : Prop) : (term811 A P Q) = (term812 A P Q).
Proof. exact (@lem4610115 A P Q). Qed.
Lemma lem4610117 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term813 A s a t) = (term814 A s a t).
Proof. exact (@lem4610116 A (term730 A s t) (term809 A s a t)). Qed.
Lemma lem4610118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term771 A s t x) = (term724 A s t x).
Proof. exact (eq_refl (term771 A s t x)). Qed.
Lemma lem4610119 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term772 A s t) = (term730 A s t).
Proof. exact (fun_ext (fun x : A => @lem4610118 A s t x)). Qed.
Lemma lem4610120 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term773 A s t) = (term731 A s t).
Proof. exact (MK_COMB (@lem4610120 A) (@lem4610119 A s t)). Qed.
Lemma lem4610122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term815 A s t) = (term762 A s t).
Proof. exact (MK_COMB (@lem4610122) (@lem4610121 A s t)). Qed.
Lemma lem4610124 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term809 A s a t) = (term809 A s a t).
Proof. exact (eq_refl (term809 A s a t)). Qed.
Lemma lem4610125 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term813 A s a t) = (term810 A s a t).
Proof. exact (MK_COMB (@lem4610123 A s t) (@lem4610124 A s a t)). Qed.
Lemma lem4610126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4610127 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term816 A s a t) = (term817 A s a t).
Proof. exact (MK_COMB (@lem4610126) (@lem4610125 A s a t)). Qed.
Lemma lem4610128 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term771 A s t x) = (term724 A s t x).
Proof. exact (eq_refl (term771 A s t x)). Qed.
Lemma lem4610129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610130 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term818 A s t x) = (term819 A s t x).
Proof. exact (MK_COMB (@lem4610129) (@lem4610128 A s t x)). Qed.
Lemma lem4610131 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term809 A s a t) = (term809 A s a t).
Proof. exact (eq_refl (term809 A s a t)). Qed.
Lemma lem4610132 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term820 A x s a t) = (term821 A x s a t).
Proof. exact (MK_COMB (@lem4610130 A s t x) (@lem4610131 A s a t)). Qed.
Lemma lem4610133 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term822 A s a t) = (term823 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4610132 A x s a t)). Qed.
Lemma lem4610134 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610135 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term814 A s a t) = (term824 A s a t).
Proof. exact (MK_COMB (@lem4610134 A) (@lem4610133 A s a t)). Qed.
Lemma lem4610136 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term813 A s a t) = (term814 A s a t)) = ((term810 A s a t) = (term824 A s a t)).
Proof. exact (MK_COMB (@lem4610127 A s a t) (@lem4610135 A s a t)). Qed.
Lemma lem4610137 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term810 A s a t) = (term824 A s a t).
Proof. exact (EQ_MP (@lem4610136 A s a t) (@lem4610117 A s a t)). Qed.
Lemma lem4610139 {A : Type'} (P : Prop) (Q : A -> Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4610140 {A : Type'} (P : Prop) (Q : type162 A) : (term825 A P Q) = (term826 A P Q).
Proof. exact (@lem4610139 (type684 A) P Q). Qed.
Lemma lem4610141 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term827 A x s a t) = (term828 A x s a t).
Proof. exact (@lem4610140 A (term724 A s t x) (term808 A s a t)). Qed.
Lemma lem4610142 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) : (term829 A s a t x) = (term806 A s a t x).
Proof. exact (eq_refl (term829 A s a t x)). Qed.
Lemma lem4610143 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term830 A s a t) = (term808 A s a t).
Proof. exact (fun_ext (fun x : type684 A => @lem4610142 A s a t x)). Qed.
Lemma lem4610144 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4610145 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term831 A s a t) = (term809 A s a t).
Proof. exact (MK_COMB (@lem4610144 A) (@lem4610143 A s a t)). Qed.
Lemma lem4610146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term819 A s t x) = (term819 A s t x).
Proof. exact (eq_refl (term819 A s t x)). Qed.
Lemma lem4610147 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term827 A x s a t) = (term821 A x s a t).
Proof. exact (MK_COMB (@lem4610146 A s t x) (@lem4610145 A s a t)). Qed.
Lemma lem4610148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4610149 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term832 A x s a t) = (term833 A x s a t).
Proof. exact (MK_COMB (@lem4610148) (@lem4610147 A x s a t)). Qed.
Lemma lem4610150 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : type684 A) : (term829 A s a t x) = (term806 A s a t x).
Proof. exact (eq_refl (term829 A s a t x)). Qed.
Lemma lem4610151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term819 A s t x) = (term819 A s t x).
Proof. exact (eq_refl (term819 A s t x)). Qed.
Lemma lem4610152 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) : (term834 A x s a t x') = (term835 A x s a t x').
Proof. exact (MK_COMB (@lem4610151 A s t x) (@lem4610150 A s a t x')). Qed.
Lemma lem4610153 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term836 A x s a t) = (term837 A x s a t).
Proof. exact (fun_ext (fun x' : type684 A => @lem4610152 A x s a t x')). Qed.
Lemma lem4610154 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4610155 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term828 A x s a t) = (term838 A x s a t).
Proof. exact (MK_COMB (@lem4610154 A) (@lem4610153 A x s a t)). Qed.
Lemma lem4610156 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : ((term827 A x s a t) = (term828 A x s a t)) = ((term821 A x s a t) = (term838 A x s a t)).
Proof. exact (MK_COMB (@lem4610149 A x s a t) (@lem4610155 A x s a t)). Qed.
Lemma lem4610157 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) : (term821 A x s a t) = (term838 A x s a t).
Proof. exact (EQ_MP (@lem4610156 A x s a t) (@lem4610141 A x s a t)). Qed.
Lemma lem4610158 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term823 A s a t) = (term839 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4610157 A x s a t)). Qed.
Lemma lem4610159 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4610160 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term824 A s a t) = (term840 A s a t).
Proof. exact (MK_COMB (@lem4610159 A) (@lem4610158 A s a t)). Qed.
Lemma lem4610161 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term810 A s a t) = (term840 A s a t).
Proof. exact (TRANS (@lem4610137 A s a t) (@lem4610160 A s a t)). Qed.
Lemma lem4610163 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term764 A s a t) = (term840 A s a t).
Proof. exact (TRANS (@lem4610113 A s a t) (@lem4610161 A s a t)). Qed.
Lemma lem4610164 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term711 A s a t) = (term840 A s a t).
Proof. exact (TRANS (@lem4609897 A s a t) (@lem4610163 A s a t)). Qed.
Lemma lem4610165 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term711 A s a t) : term840 A s a t.
Proof. exact (EQ_MP (@lem4610164 A s a t) (@lem4609747 A s a t h1)). Qed.
Lemma lem4610166 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term838 A x s a t) : term838 A x s a t.
Proof. exact (h1). Qed.
Lemma lem4610167 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term835 A x s a t x'.
Proof. exact (h1). Qed.
Lemma lem4610168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610174 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610173 A Prop f x). Qed.
Lemma lem4610176 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4610174 A s a). Qed.
Lemma lem4610177 {A : Type'} (s : A -> Prop) (a : A) : (term635 A s a) = (term841 A s a).
Proof. exact (MK_COMB (@lem4610168) (@lem4610176 A s a)). Qed.
Lemma lem4610183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610184 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610183 A Prop f x). Qed.
Lemma lem4610186 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4610184 A t x). Qed.
Lemma lem4610191 {A : Type'} (x : A) (a : A) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem4610192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610197 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610198 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610197 A Prop f x). Qed.
Lemma lem4610200 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4610198 A s x). Qed.
Lemma lem4610201 {A : Type'} (s : A -> Prop) (x : A) : (term635 A s x) = (term841 A s x).
Proof. exact (MK_COMB (@lem4610192) (@lem4610200 A s x)). Qed.
Lemma lem4610202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610203 {A : Type'} (s : A -> Prop) (x : A) : (term713 A s x) = (term842 A s x).
Proof. exact (MK_COMB (@lem4610202) (@lem4610201 A s x)). Qed.
Lemma lem4610204 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term715 A s x a) = (term843 A s x a).
Proof. exact (MK_COMB (@lem4610203 A s x) (@lem4610191 A x a)). Qed.
Lemma lem4610205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610206 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term718 A s x a) = (term844 A s x a).
Proof. exact (MK_COMB (@lem4610205) (@lem4610204 A s x a)). Qed.
Lemma lem4610207 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term720 A s a t x) = (term845 A s a t x).
Proof. exact (MK_COMB (@lem4610206 A s x a) (@lem4610186 A t x)). Qed.
Lemma lem4610208 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term721 A s a t) = (term846 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4610207 A s a t x)). Qed.
Lemma lem4610209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4610210 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term722 A s a t) = (term847 A s a t).
Proof. exact (MK_COMB (@lem4610209 A) (@lem4610208 A s a t)). Qed.
Lemma lem4610211 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term847 A s a t.
Proof. exact (EQ_MP (@lem4610210 A s a t) (@lem4609808 A s a t h1)). Qed.
Lemma lem4610212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610213 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4610218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610219 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610218 (A -> Prop) A f x). Qed.
Lemma lem4610221 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610219 A x' x). Qed.
Lemma lem4610222 {A : Type'} (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A t x' x) = (term849 A t x' x).
Proof. exact (MK_COMB (@lem4610213 A t) (@lem4610221 A x' x)). Qed.
Lemma lem4610224 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610225 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610224 A Prop f x). Qed.
Lemma lem4610226 {A : Type'} (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term849 A t x' x) = (term850 A t x' x).
Proof. exact (@lem4610225 A t (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610227 {A : Type'} (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A t x' x) = (term850 A t x' x).
Proof. exact (TRANS (@lem4610222 A t x' x) (@lem4610226 A t x' x)). Qed.
Lemma lem4610228 {A : Type'} (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term851 A t x' x) = (term852 A t x' x).
Proof. exact (MK_COMB (@lem4610212) (@lem4610227 A t x' x)). Qed.
Lemma lem4610229 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4610234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610235 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610234 (A -> Prop) A f x). Qed.
Lemma lem4610237 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610235 A x' x). Qed.
Lemma lem4610238 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term854 A x' x).
Proof. exact (MK_COMB (@lem4610229 A x) (@lem4610237 A x' x)). Qed.
Lemma lem4610240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610241 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610240 A Prop f x). Qed.
Lemma lem4610242 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term854 A x' x) = (term855 A x' x).
Proof. exact (@lem4610241 A x (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610243 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term855 A x' x).
Proof. exact (TRANS (@lem4610238 A x' x) (@lem4610242 A x' x)). Qed.
Lemma lem4610244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610245 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term856 A x' x) = (term857 A x' x).
Proof. exact (MK_COMB (@lem4610244) (@lem4610243 A x' x)). Qed.
Lemma lem4610246 {A : Type'} (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term858 A t x' x) = (term859 A t x' x).
Proof. exact (MK_COMB (@lem4610245 A x' x) (@lem4610228 A t x' x)). Qed.
Lemma lem4610247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610248 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4610253 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610254 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610253 (A -> Prop) A f x). Qed.
Lemma lem4610256 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610254 A x' x). Qed.
Lemma lem4610257 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term854 A x' x).
Proof. exact (MK_COMB (@lem4610248 A x) (@lem4610256 A x' x)). Qed.
Lemma lem4610259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610260 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610259 A Prop f x). Qed.
Lemma lem4610261 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term854 A x' x) = (term855 A x' x).
Proof. exact (@lem4610260 A x (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610262 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term855 A x' x).
Proof. exact (TRANS (@lem4610257 A x' x) (@lem4610261 A x' x)). Qed.
Lemma lem4610263 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term860 A x' x) = (term861 A x' x).
Proof. exact (MK_COMB (@lem4610247) (@lem4610262 A x' x)). Qed.
Lemma lem4610264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610265 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4610270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610271 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610270 (A -> Prop) A f x). Qed.
Lemma lem4610273 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610271 A x' x). Qed.
Lemma lem4610274 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4610275 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term862 A x' x) = (term863 A x' x).
Proof. exact (MK_COMB (@lem4610265 A) (@lem4610273 A x' x)). Qed.
Lemma lem4610276 {A : Type'} (x' : type684 A) (x : A -> Prop) (a : A) : ((x' x) = a) = ((@I ((A -> Prop) -> A) x' x) = a).
Proof. exact (MK_COMB (@lem4610275 A x' x) (@lem4610274 A a)). Qed.
Lemma lem4610277 {A : Type'} (x' : type684 A) (x : A -> Prop) (a : A) : (term864 A x' x a) = (term865 A x' x a).
Proof. exact (MK_COMB (@lem4610264) (@lem4610276 A x' x a)). Qed.
Lemma lem4610278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610279 {A : Type'} (x' : type684 A) (x : A -> Prop) (a : A) : (term866 A x' x a) = (term867 A x' x a).
Proof. exact (MK_COMB (@lem4610278) (@lem4610277 A x' x a)). Qed.
Lemma lem4610280 {A : Type'} (a : A) (x' : type684 A) (x : A -> Prop) : (term868 A a x' x) = (term869 A a x' x).
Proof. exact (MK_COMB (@lem4610279 A x' x a) (@lem4610263 A x' x)). Qed.
Lemma lem4610281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610282 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4610287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610288 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610287 (A -> Prop) A f x). Qed.
Lemma lem4610290 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610288 A x' x). Qed.
Lemma lem4610291 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A s x' x) = (term849 A s x' x).
Proof. exact (MK_COMB (@lem4610282 A s) (@lem4610290 A x' x)). Qed.
Lemma lem4610293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610294 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610293 A Prop f x). Qed.
Lemma lem4610295 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term849 A s x' x) = (term850 A s x' x).
Proof. exact (@lem4610294 A s (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610296 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A s x' x) = (term850 A s x' x).
Proof. exact (TRANS (@lem4610291 A s x' x) (@lem4610295 A s x' x)). Qed.
Lemma lem4610297 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term851 A s x' x) = (term852 A s x' x).
Proof. exact (MK_COMB (@lem4610281) (@lem4610296 A s x' x)). Qed.
Lemma lem4610298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610299 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term870 A s x' x) = (term871 A s x' x).
Proof. exact (MK_COMB (@lem4610298) (@lem4610297 A s x' x)). Qed.
Lemma lem4610300 {A : Type'} (s : A -> Prop) (a : A) (x' : type684 A) (x : A -> Prop) : (term872 A s a x' x) = (term873 A s a x' x).
Proof. exact (MK_COMB (@lem4610299 A s x' x) (@lem4610280 A a x' x)). Qed.
Lemma lem4610301 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4610306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610307 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610306 (A -> Prop) A f x). Qed.
Lemma lem4610309 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610307 A x' x). Qed.
Lemma lem4610310 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term854 A x' x).
Proof. exact (MK_COMB (@lem4610301 A x) (@lem4610309 A x' x)). Qed.
Lemma lem4610312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610313 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610312 A Prop f x). Qed.
Lemma lem4610314 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term854 A x' x) = (term855 A x' x).
Proof. exact (@lem4610313 A x (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610315 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term853 A x' x) = (term855 A x' x).
Proof. exact (TRANS (@lem4610310 A x' x) (@lem4610314 A x' x)). Qed.
Lemma lem4610316 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4610321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610322 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610321 (A -> Prop) A f x). Qed.
Lemma lem4610324 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610322 A x' x). Qed.
Lemma lem4610325 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4610326 {A : Type'} (x' : type684 A) (x : A -> Prop) : (term862 A x' x) = (term863 A x' x).
Proof. exact (MK_COMB (@lem4610316 A) (@lem4610324 A x' x)). Qed.
Lemma lem4610327 {A : Type'} (x' : type684 A) (x : A -> Prop) (a : A) : ((x' x) = a) = ((@I ((A -> Prop) -> A) x' x) = a).
Proof. exact (MK_COMB (@lem4610326 A x' x) (@lem4610325 A a)). Qed.
Lemma lem4610328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610329 {A : Type'} (x' : type684 A) (x : A -> Prop) (a : A) : (term874 A x' x a) = (term875 A x' x a).
Proof. exact (MK_COMB (@lem4610328) (@lem4610327 A x' x a)). Qed.
Lemma lem4610330 {A : Type'} (a : A) (x' : type684 A) (x : A -> Prop) : (term876 A a x' x) = (term877 A a x' x).
Proof. exact (MK_COMB (@lem4610329 A x' x a) (@lem4610315 A x' x)). Qed.
Lemma lem4610331 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4610336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610337 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4610336 (A -> Prop) A f x). Qed.
Lemma lem4610339 {A : Type'} (x' : type684 A) (x : A -> Prop) : (x' x) = (@I ((A -> Prop) -> A) x' x).
Proof. exact (@lem4610337 A x' x). Qed.
Lemma lem4610340 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A s x' x) = (term849 A s x' x).
Proof. exact (MK_COMB (@lem4610331 A s) (@lem4610339 A x' x)). Qed.
Lemma lem4610342 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610343 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610342 A Prop f x). Qed.
Lemma lem4610344 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term849 A s x' x) = (term850 A s x' x).
Proof. exact (@lem4610343 A s (@I ((A -> Prop) -> A) x' x)). Qed.
Lemma lem4610345 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term848 A s x' x) = (term850 A s x' x).
Proof. exact (TRANS (@lem4610340 A s x' x) (@lem4610344 A s x' x)). Qed.
Lemma lem4610346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610347 {A : Type'} (s : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term878 A s x' x) = (term879 A s x' x).
Proof. exact (MK_COMB (@lem4610346) (@lem4610345 A s x' x)). Qed.
Lemma lem4610348 {A : Type'} (s : A -> Prop) (a : A) (x' : type684 A) (x : A -> Prop) : (term880 A s a x' x) = (term881 A s a x' x).
Proof. exact (MK_COMB (@lem4610347 A s x' x) (@lem4610330 A a x' x)). Qed.
Lemma lem4610349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610350 {A : Type'} (s : A -> Prop) (a : A) (x' : type684 A) (x : A -> Prop) : (term882 A s a x' x) = (term883 A s a x' x).
Proof. exact (MK_COMB (@lem4610349) (@lem4610348 A s a x' x)). Qed.
Lemma lem4610351 {A : Type'} (s : A -> Prop) (a : A) (x' : type684 A) (x : A -> Prop) : (term884 A s a x' x) = (term885 A s a x' x).
Proof. exact (MK_COMB (@lem4610350 A s a x' x) (@lem4610300 A s a x' x)). Qed.
Lemma lem4610352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4610353 {A : Type'} (s : A -> Prop) (a : A) (x' : type684 A) (x : A -> Prop) : (term886 A s a x' x) = (term887 A s a x' x).
Proof. exact (MK_COMB (@lem4610352) (@lem4610351 A s a x' x)). Qed.
Lemma lem4610354 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (x : A -> Prop) : (term802 A s a t x' x) = (term888 A s a t x' x).
Proof. exact (MK_COMB (@lem4610353 A s a x' x) (@lem4610246 A t x' x)). Qed.
Lemma lem4610355 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) : (term804 A s a t x') = (term889 A s a t x').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4610354 A s a t x' x)). Qed.
Lemma lem4610356 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4610357 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) : (term806 A s a t x') = (term890 A s a t x').
Proof. exact (MK_COMB (@lem4610356 A) (@lem4610355 A s a t x')). Qed.
Lemma lem4610358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4610363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610364 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610363 A Prop f x). Qed.
Lemma lem4610366 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4610364 A t x). Qed.
Lemma lem4610367 {A : Type'} (t : A -> Prop) (x : A) : (term635 A t x) = (term841 A t x).
Proof. exact (MK_COMB (@lem4610358) (@lem4610366 A t x)). Qed.
Lemma lem4610372 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4610373 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4610372 A Prop f x). Qed.
Lemma lem4610375 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4610373 A s x). Qed.
Lemma lem4610376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610377 {A : Type'} (s : A -> Prop) (x : A) : (term341 A s x) = (term891 A s x).
Proof. exact (MK_COMB (@lem4610376) (@lem4610375 A s x)). Qed.
Lemma lem4610378 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term724 A s t x) = (term892 A s t x).
Proof. exact (MK_COMB (@lem4610377 A s x) (@lem4610367 A t x)). Qed.
Lemma lem4610379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610380 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term819 A s t x) = (term893 A s t x).
Proof. exact (MK_COMB (@lem4610379) (@lem4610378 A s t x)). Qed.
Lemma lem4610381 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) : (term835 A x s a t x') = (term894 A x s a t x').
Proof. exact (MK_COMB (@lem4610380 A s t x) (@lem4610357 A s a t x')). Qed.
Lemma lem4610382 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term894 A x s a t x'.
Proof. exact (EQ_MP (@lem4610381 A x s a t x') (@lem4610167 A x s a t x' h1)). Qed.
Lemma lem4610384 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term892 A s t x.
Proof. exact (proj1 (@lem4610382 A x s a t x' h1)). Qed.
Lemma lem4610404 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term845 A s a t x) = (term845 A s a t x).
Proof. exact (eq_refl (term845 A s a t x)). Qed.
Lemma lem4610405 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term846 A s a t) = (term846 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4610404 A s a t x)). Qed.
Lemma lem4610406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4610408 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term847 A s a t) = (term847 A s a t).
Proof. exact (MK_COMB (@lem4610406 A) (@lem4610405 A s a t)). Qed.
Lemma lem4610409 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term847 A s a t.
Proof. exact (EQ_MP (@lem4610408 A s a t) (@lem4610211 A s a t h1)). Qed.
Lemma lem4610497 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term895 A s a t _55384.
Proof. exact (@lem4610409 A s a t h1 _55384). Qed.
Lemma lem4610498 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55384 : A) : (term895 A s a t _55384) = (term845 A s a t _55384).
Proof. exact (eq_refl (term895 A s a t _55384)). Qed.
Lemma lem4610499 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term845 A s a t _55384.
Proof. exact (EQ_MP (@lem4610498 A s a t _55384) (@lem4610497 A _55384 s a t h1)). Qed.
Lemma lem4610525 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55384 : A) : (term845 A s a t _55384) = (term896 A s a t _55384).
Proof. exact (@lem4609194 (term841 A s _55384) (_55384 = a) (@I (A -> Prop) t _55384)). Qed.
Lemma lem4610526 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term896 A s a t _55384.
Proof. exact (EQ_MP (@lem4610525 A s a t _55384) (@lem4610499 A _55384 s a t h1)). Qed.
Lemma lem4610530 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term841 A t x.
Proof. exact (proj2 (@lem4610384 A x s a t x' h1)). Qed.
Lemma lem4610615 {A : Type'} : (@I (A -> Prop)) = (@I (A -> Prop)).
Proof. exact (eq_refl (@I (A -> Prop))). Qed.
Lemma lem4610616 {A : Type'} (_55386 : A -> Prop) (_55388 : A -> Prop) (h1 : _55386 = _55388) : _55386 = _55388.
Proof. exact (h1). Qed.
Lemma lem4610617 {A : Type'} (_55387 : A) (_55389 : A) (h1 : _55387 = _55389) : _55387 = _55389.
Proof. exact (h1). Qed.
Lemma lem4610618 {A : Type'} (_55386 : A -> Prop) (_55388 : A -> Prop) (h1 : _55386 = _55388) : (@I (A -> Prop) _55386) = (@I (A -> Prop) _55388).
Proof. exact (MK_COMB (@lem4610615 A) (@lem4610616 A _55386 _55388 h1)). Qed.
Lemma lem4610619 {A : Type'} (_55387 : A) (_55389 : A) (_55386 : A -> Prop) (_55388 : A -> Prop) (h1 : _55387 = _55389) (h2 : _55386 = _55388) : (@I (A -> Prop) _55386 _55387) = (@I (A -> Prop) _55388 _55389).
Proof. exact (MK_COMB (@lem4610618 A _55386 _55388 h2) (@lem4610617 A _55387 _55389 h1)). Qed.
Lemma lem4610621 (b : Prop) (a : Prop) : term897 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4610622 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : term898 A _55388 _55389 _55386 _55387.
Proof. exact (@lem4610621 (@I (A -> Prop) _55388 _55389) (@I (A -> Prop) _55386 _55387)). Qed.
Lemma lem4610623 {A : Type'} (_55387 : A) (_55389 : A) (_55386 : A -> Prop) (_55388 : A -> Prop) (h1 : _55387 = _55389) (h2 : _55386 = _55388) : term899 A _55388 _55389 _55386 _55387.
Proof. exact (@lem4610622 A _55388 _55389 _55386 _55387 (@lem4610619 A _55387 _55389 _55386 _55388 h1 h2)). Qed.
Lemma lem4610624 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) (h1 : _55387 = _55389) : term900 A _55388 _55389 _55386 _55387.
Proof. exact (fun h0 : _55386 = _55388 => @lem4610623 A _55387 _55389 _55386 _55388 h1 h0). Qed.
Lemma lem4610626 (a : Prop) (b : Prop) : (a -> b) = (term901 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4610627 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term900 A _55388 _55389 _55386 _55387) = (term902 A _55388 _55389 _55386 _55387).
Proof. exact (@lem4610626 (_55386 = _55388) (term899 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610628 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) (h1 : _55387 = _55389) : term902 A _55388 _55389 _55386 _55387.
Proof. exact (EQ_MP (@lem4610627 A _55388 _55389 _55386 _55387) (@lem4610624 A _55388 _55386 _55387 _55389 h1)). Qed.
Lemma lem4610629 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : term903 A _55388 _55389 _55386 _55387.
Proof. exact (fun h0 : _55387 = _55389 => @lem4610628 A _55388 _55386 _55387 _55389 h0). Qed.
Lemma lem4610631 (a : Prop) (b : Prop) : (a -> b) = (term901 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4610632 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term903 A _55388 _55389 _55386 _55387) = (term904 A _55388 _55389 _55386 _55387).
Proof. exact (@lem4610631 (_55387 = _55389) (term902 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610633 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : term904 A _55388 _55389 _55386 _55387.
Proof. exact (EQ_MP (@lem4610632 A _55388 _55389 _55386 _55387) (@lem4610629 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610656 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4610384 A x s a t x' h1)). Qed.
Lemma lem4610657 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term905 A s x.
Proof. exact (fun h0 : term841 A s x => @lem4610656 A x s a t x' h1). Qed.
Lemma lem4610659 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4610660 {A : Type'} (s : A -> Prop) (x : A) : (term905 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4610659 (@I (A -> Prop) s x)). Qed.
Lemma lem4610661 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4610660 A s x) (@lem4610657 A x s a t x' h1)). Qed.
Lemma lem4610663 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4610664 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4610663 A x). Qed.
Lemma lem4610665 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem4610664 A s). Qed.
Lemma lem4610666 {A : Type'} (s : A -> Prop) : term906 A s.
Proof. exact (fun h0 : term907 A s => @lem4610665 A s). Qed.
Lemma lem4610668 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4610669 {A : Type'} (s : A -> Prop) : (term906 A s) = (s = s).
Proof. exact (@lem4610668 (s = s)). Qed.
Lemma lem4610670 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem4610669 A s) (@lem4610666 A s)). Qed.
Lemma lem4610672 {A : Type'} (s : A -> Prop) (a : A) (h1 : term635 A s a) : term841 A s a.
Proof. exact (EQ_MP (@lem4610177 A s a) (@lem4609753 A s a h1)). Qed.
Lemma lem4610673 {A : Type'} (s : A -> Prop) (a : A) (h1 : term635 A s a) : term908 A s a.
Proof. exact (fun h0 : @I (A -> Prop) s a => @lem4610672 A s a h1). Qed.
Lemma lem4610675 (p : Prop) : (term909 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4610676 {A : Type'} (s : A -> Prop) (a : A) : (term908 A s a) = (term841 A s a).
Proof. exact (@lem4610675 (@I (A -> Prop) s a)). Qed.
Lemma lem4610677 {A : Type'} (s : A -> Prop) (a : A) (h1 : term635 A s a) : term841 A s a.
Proof. exact (EQ_MP (@lem4610676 A s a) (@lem4610673 A s a h1)). Qed.
Lemma lem4610679 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem4610384 A x s a t x' h1)). Qed.
Lemma lem4610680 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term905 A s x.
Proof. exact (fun h0 : term841 A s x => @lem4610679 A x s a t x' h1). Qed.
Lemma lem4610682 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4610683 {A : Type'} (s : A -> Prop) (x : A) : (term905 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4610682 (@I (A -> Prop) s x)). Qed.
Lemma lem4610684 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4610683 A s x) (@lem4610680 A x s a t x' h1)). Qed.
Lemma lem4610686 (b : Prop) (a : Prop) : (a \/ b) = (term647 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4610687 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) : (term904 A _55388 _55389 _55386 _55387) = (term910 A _55388 _55386 _55387 _55389).
Proof. exact (@lem4610686 (term902 A _55388 _55389 _55386 _55387) (term342 A _55387 _55389)). Qed.
Lemma lem4610689 (a : Prop) (b : Prop) : (term911 a b) = (term912 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4610690 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term913 A _55388 _55389 _55386 _55387) = (term914 A _55388 _55389 _55386 _55387).
Proof. exact (@lem4610689 (term915 A _55386 _55388) (term899 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610692 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4610693 {A : Type'} (_55386 : A -> Prop) (_55388 : A -> Prop) : (term916 A _55386 _55388) = (_55386 = _55388).
Proof. exact (@lem4610692 (_55386 = _55388)). Qed.
Lemma lem4610694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610695 {A : Type'} (_55386 : A -> Prop) (_55388 : A -> Prop) : (term917 A _55386 _55388) = (term918 A _55386 _55388).
Proof. exact (MK_COMB (@lem4610694) (@lem4610693 A _55386 _55388)). Qed.
Lemma lem4610697 (a : Prop) (b : Prop) : (term911 a b) = (term912 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4610698 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term919 A _55388 _55389 _55386 _55387) = (term920 A _55388 _55389 _55386 _55387).
Proof. exact (@lem4610697 (@I (A -> Prop) _55388 _55389) (term841 A _55386 _55387)). Qed.
Lemma lem4610700 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4610701 {A : Type'} (_55386 : A -> Prop) (_55387 : A) : (term921 A _55386 _55387) = (@I (A -> Prop) _55386 _55387).
Proof. exact (@lem4610700 (@I (A -> Prop) _55386 _55387)). Qed.
Lemma lem4610702 {A : Type'} (_55388 : A -> Prop) (_55389 : A) : (term922 A _55388 _55389) = (term922 A _55388 _55389).
Proof. exact (eq_refl (term922 A _55388 _55389)). Qed.
Lemma lem4610703 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term920 A _55388 _55389 _55386 _55387) = (term923 A _55388 _55389 _55386 _55387).
Proof. exact (MK_COMB (@lem4610702 A _55388 _55389) (@lem4610701 A _55386 _55387)). Qed.
Lemma lem4610704 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term919 A _55388 _55389 _55386 _55387) = (term923 A _55388 _55389 _55386 _55387).
Proof. exact (TRANS (@lem4610698 A _55388 _55389 _55386 _55387) (@lem4610703 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610705 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term914 A _55388 _55389 _55386 _55387) = (term924 A _55388 _55389 _55386 _55387).
Proof. exact (MK_COMB (@lem4610695 A _55386 _55388) (@lem4610704 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610706 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term913 A _55388 _55389 _55386 _55387) = (term924 A _55388 _55389 _55386 _55387).
Proof. exact (TRANS (@lem4610690 A _55388 _55389 _55386 _55387) (@lem4610705 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4610708 {A : Type'} (_55388 : A -> Prop) (_55389 : A) (_55386 : A -> Prop) (_55387 : A) : (term925 A _55388 _55389 _55386 _55387) = (term926 A _55388 _55389 _55386 _55387).
Proof. exact (MK_COMB (@lem4610707) (@lem4610706 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610709 {A : Type'} (_55387 : A) (_55389 : A) : (term342 A _55387 _55389) = (term342 A _55387 _55389).
Proof. exact (eq_refl (term342 A _55387 _55389)). Qed.
Lemma lem4610710 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) : (term910 A _55388 _55386 _55387 _55389) = (term927 A _55388 _55386 _55387 _55389).
Proof. exact (MK_COMB (@lem4610708 A _55388 _55389 _55386 _55387) (@lem4610709 A _55387 _55389)). Qed.
Lemma lem4610711 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) : (term904 A _55388 _55389 _55386 _55387) = (term927 A _55388 _55386 _55387 _55389).
Proof. exact (TRANS (@lem4610687 A _55388 _55386 _55387 _55389) (@lem4610710 A _55388 _55386 _55387 _55389)). Qed.
Lemma lem4610713 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term928 A a s x.
Proof. exact (conj (@lem4610677 A s a h1) (@lem4610684 A x s a t x' h2)). Qed.
Lemma lem4610714 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term929 A a s x.
Proof. exact (conj (@lem4610670 A s) (@lem4610713 A x s a t x' h1 h2)). Qed.
Lemma lem4610716 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) : term927 A _55388 _55386 _55387 _55389.
Proof. exact (EQ_MP (@lem4610711 A _55388 _55386 _55387 _55389) (@lem4610633 A _55388 _55389 _55386 _55387)). Qed.
Lemma lem4610717 {A : Type'} (_55388 : A -> Prop) (_55386 : A -> Prop) (_55387 : A) (_55389 : A) : term927 A _55388 _55386 _55387 _55389.
Proof. exact (@lem4610716 A _55388 _55386 _55387 _55389). Qed.
Lemma lem4610718 {A : Type'} (s : A -> Prop) (x : A) (a : A) : term930 A s x a.
Proof. exact (@lem4610717 A s s x a). Qed.
Lemma lem4610721 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term342 A x a.
Proof. exact (@lem4610718 A s x a (@lem4610714 A x s a t x' h1 h2)). Qed.
Lemma lem4610722 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term931 A x a.
Proof. exact (fun h0 : x = a => @lem4610721 A x s a t x' h1 h2). Qed.
Lemma lem4610724 (p : Prop) : (term909 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4610725 {A : Type'} (x : A) (a : A) : (term931 A x a) = (term342 A x a).
Proof. exact (@lem4610724 (x = a)). Qed.
Lemma lem4610726 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term342 A x a.
Proof. exact (EQ_MP (@lem4610725 A x a) (@lem4610722 A x s a t x' h1 h2)). Qed.
Lemma lem4610732 (q : Prop) (p : Prop) (r : Prop) : (term662 p q r) = (term662 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4610733 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) (_55384 : A) : (term896 A s a t _55384) = (term932 A a s t _55384).
Proof. exact (@lem4610732 (_55384 = a) (term841 A s _55384) (@I (A -> Prop) t _55384)). Qed.
Lemma lem4610749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4610750 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term933 A s t _55384) = (term934 A t s _55384).
Proof. exact (@lem4610749 (@I (A -> Prop) t _55384) (term841 A s _55384)). Qed.
Lemma lem4610756 {A : Type'} (_55384 : A) (a : A) : (term359 A _55384 a) = (term359 A _55384 a).
Proof. exact (eq_refl (term359 A _55384 a)). Qed.
Lemma lem4610757 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term932 A a s t _55384) = (term935 A a t s _55384).
Proof. exact (MK_COMB (@lem4610756 A _55384 a) (@lem4610750 A t s _55384)). Qed.
Lemma lem4610768 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term896 A s a t _55384) = (term935 A a t s _55384).
Proof. exact (TRANS (@lem4610733 A a s t _55384) (@lem4610757 A a t s _55384)). Qed.
Lemma lem4610769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4610770 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term936 A s a t _55384) = (term937 A a t s _55384).
Proof. exact (MK_COMB (@lem4610769) (@lem4610768 A a t s _55384)). Qed.
Lemma lem4610784 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4610785 {A : Type'} (a : A) (s : A -> Prop) (_55384 : A) : (term843 A s _55384 a) = (term938 A a s _55384).
Proof. exact (@lem4610784 (_55384 = a) (term841 A s _55384)). Qed.
Lemma lem4610793 {A : Type'} (t : A -> Prop) (_55384 : A) : (term939 A t _55384) = (term939 A t _55384).
Proof. exact (eq_refl (term939 A t _55384)). Qed.
Lemma lem4610794 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55384 : A) : (term940 A t s _55384 a) = (term941 A t a s _55384).
Proof. exact (MK_COMB (@lem4610793 A t _55384) (@lem4610785 A a s _55384)). Qed.
Lemma lem4610798 (q : Prop) (p : Prop) (r : Prop) : (term662 p q r) = (term662 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4610799 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term941 A t a s _55384) = (term935 A a t s _55384).
Proof. exact (@lem4610798 (_55384 = a) (@I (A -> Prop) t _55384) (term841 A s _55384)). Qed.
Lemma lem4610817 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : (term940 A t s _55384 a) = (term935 A a t s _55384).
Proof. exact (TRANS (@lem4610794 A t a s _55384) (@lem4610799 A a t s _55384)). Qed.
Lemma lem4610818 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : ((term896 A s a t _55384) = (term940 A t s _55384 a)) = ((term935 A a t s _55384) = (term935 A a t s _55384)).
Proof. exact (MK_COMB (@lem4610770 A a t s _55384) (@lem4610817 A a t s _55384)). Qed.
Lemma lem4610820 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4610821 (x : Prop) : (x = x) = True.
Proof. exact (@lem4610820 Prop x). Qed.
Lemma lem4610822 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55384 : A) : ((term935 A a t s _55384) = (term935 A a t s _55384)) = True.
Proof. exact (@lem4610821 (term935 A a t s _55384)). Qed.
Lemma lem4610823 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55384 : A) (a : A) : ((term896 A s a t _55384) = (term940 A t s _55384 a)) = True.
Proof. exact (TRANS (@lem4610818 A a t s _55384) (@lem4610822 A a t s _55384)). Qed.
Lemma lem4610824 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55384 : A) (a : A) : True = ((term896 A s a t _55384) = (term940 A t s _55384 a)).
Proof. exact (SYM (@lem4610823 A t s _55384 a)). Qed.
Lemma lem4610825 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55384 : A) (a : A) : (term896 A s a t _55384) = (term940 A t s _55384 a).
Proof. exact (EQ_MP (@lem4610824 A t s _55384 a) (@lem0)). Qed.
Lemma lem4610826 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term940 A t s _55384 a.
Proof. exact (EQ_MP (@lem4610825 A t s _55384 a) (@lem4610526 A _55384 s a t h1)). Qed.
Lemma lem4610828 (b : Prop) (a : Prop) : (a \/ b) = (term647 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4610829 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55384 : A) : (term940 A t s _55384 a) = (term942 A s a t _55384).
Proof. exact (@lem4610828 (term843 A s _55384 a) (@I (A -> Prop) t _55384)). Qed.
Lemma lem4610831 (a : Prop) (b : Prop) : (term911 a b) = (term912 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4610832 {A : Type'} (s : A -> Prop) (_55384 : A) (a : A) : (term943 A s _55384 a) = (term944 A s _55384 a).
Proof. exact (@lem4610831 (term841 A s _55384) (_55384 = a)). Qed.
Lemma lem4610834 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4610835 {A : Type'} (s : A -> Prop) (_55384 : A) : (term921 A s _55384) = (@I (A -> Prop) s _55384).
Proof. exact (@lem4610834 (@I (A -> Prop) s _55384)). Qed.
Lemma lem4610836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610837 {A : Type'} (s : A -> Prop) (_55384 : A) : (term945 A s _55384) = (term891 A s _55384).
Proof. exact (MK_COMB (@lem4610836) (@lem4610835 A s _55384)). Qed.
Lemma lem4610838 {A : Type'} (_55384 : A) (a : A) : (term342 A _55384 a) = (term342 A _55384 a).
Proof. exact (eq_refl (term342 A _55384 a)). Qed.
Lemma lem4610839 {A : Type'} (s : A -> Prop) (_55384 : A) (a : A) : (term944 A s _55384 a) = (term946 A s _55384 a).
Proof. exact (MK_COMB (@lem4610837 A s _55384) (@lem4610838 A _55384 a)). Qed.
Lemma lem4610840 {A : Type'} (s : A -> Prop) (_55384 : A) (a : A) : (term943 A s _55384 a) = (term946 A s _55384 a).
Proof. exact (TRANS (@lem4610832 A s _55384 a) (@lem4610839 A s _55384 a)). Qed.
Lemma lem4610841 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4610842 {A : Type'} (s : A -> Prop) (_55384 : A) (a : A) : (term947 A s _55384 a) = (term948 A s _55384 a).
Proof. exact (MK_COMB (@lem4610841) (@lem4610840 A s _55384 a)). Qed.
Lemma lem4610843 {A : Type'} (t : A -> Prop) (_55384 : A) : (@I (A -> Prop) t _55384) = (@I (A -> Prop) t _55384).
Proof. exact (eq_refl (@I (A -> Prop) t _55384)). Qed.
Lemma lem4610844 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55384 : A) : (term942 A s a t _55384) = (term949 A s a t _55384).
Proof. exact (MK_COMB (@lem4610842 A s _55384 a) (@lem4610843 A t _55384)). Qed.
Lemma lem4610845 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55384 : A) : (term940 A t s _55384 a) = (term949 A s a t _55384).
Proof. exact (TRANS (@lem4610829 A s a t _55384) (@lem4610844 A s a t _55384)). Qed.
Lemma lem4610847 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term635 A s a) (h2 : term835 A x s a t x') : term946 A s x a.
Proof. exact (conj (@lem4610661 A x s a t x' h2) (@lem4610726 A x s a t x' h1 h2)). Qed.
Lemma lem4610849 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term949 A s a t _55384.
Proof. exact (EQ_MP (@lem4610845 A s a t _55384) (@lem4610826 A _55384 s a t h1)). Qed.
Lemma lem4610850 {A : Type'} (_55384 : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term949 A s a t _55384.
Proof. exact (@lem4610849 A _55384 s a t h1). Qed.
Lemma lem4610851 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) : term949 A s a t x.
Proof. exact (@lem4610850 A x s a t h1). Qed.
Lemma lem4610854 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : @I (A -> Prop) t x.
Proof. exact (@lem4610851 A x s a t h1 (@lem4610847 A x s a t x' h2 h3)). Qed.
Lemma lem4610855 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : term905 A t x.
Proof. exact (fun h0 : term841 A t x => @lem4610854 A x s a t x' h1 h2 h3). Qed.
Lemma lem4610857 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4610858 {A : Type'} (t : A -> Prop) (x : A) : (term905 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4610857 (@I (A -> Prop) t x)). Qed.
Lemma lem4610859 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4610858 A t x) (@lem4610855 A x s a t x' h1 h2 h3)). Qed.
Lemma lem4610862 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4610864 {A : Type'} (t : A -> Prop) (x : A) : (term841 A t x) = (term950 A t x).
Proof. exact (@lem4610862 (@I (A -> Prop) t x)). Qed.
Lemma lem4610867 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term835 A x s a t x') : term950 A t x.
Proof. exact (EQ_MP (@lem4610864 A t x) (@lem4610530 A x s a t x' h1)). Qed.
Lemma lem4610870 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : False.
Proof. exact (@lem4610867 A x s a t x' h3 (@lem4610859 A x s a t x' h1 h2 h3)). Qed.
Lemma lem4610871 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : term652.
Proof. exact (fun h0 : ~ False => @lem4610870 A x s a t x' h1 h2 h3). Qed.
Lemma lem4610873 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4610874 : term652 = False.
Proof. exact (@lem4610873 False). Qed.
Lemma lem4610875 {A : Type'} (x : A) (s : A -> Prop) (a : A) (t : A -> Prop) (x' : type684 A) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term835 A x s a t x') : False.
Proof. exact (EQ_MP (@lem4610874) (@lem4610871 A x s a t x' h1 h2 h3)). Qed.
Lemma lem4610876 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term350 A s a t) (h2 : term838 A x s a t) (h3 : term635 A s a) : False.
Proof. exact (ex_elim (@lem4610166 A x s a t h2) (fun x' : type684 A => fun h0 : term837 A x s a t x' => @lem4610875 A x s a t x' h1 h3 h0)). Qed.
Lemma lem4610877 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term711 A s a t) : False.
Proof. exact (ex_elim (@lem4610165 A s a t h3) (fun x : A => fun h0 : term839 A s a t x => @lem4610876 A x t s a h1 h0 h2)). Qed.
Lemma lem4610878 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term711 A s a t) : (term635 A s a) = False.
Proof. exact (prop_ext (fun h4 : term635 A s a => @lem4610877 A s a t h1 h2 h3) (fun h4 : False => @lem4609753 A s a h2)). Qed.
Lemma lem4610879 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term711 A s a t) : False.
Proof. exact (EQ_MP (@lem4610878 A s a t h1 h2 h3) (@lem4609753 A s a h2)). Qed.
Lemma lem4610880 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term711 A s a t) : (term711 A s a t) = False.
Proof. exact (prop_ext (fun h4 : term711 A s a t => @lem4610879 A s a t h1 h2 h3) (fun h4 : False => @lem4609747 A s a t h3)). Qed.
Lemma lem4610881 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term350 A s a t) (h2 : term635 A s a) (h3 : term711 A s a t) : False.
Proof. exact (EQ_MP (@lem4610880 A s a t h1 h2 h3) (@lem4609747 A s a t h3)). Qed.
Lemma lem4610882 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term350 A s a t) (h2 : term635 A s a) : term710 A s a t.
Proof. exact (fun h0 : term711 A s a t => @lem4610881 A s a t h1 h2 h0). Qed.
Lemma lem4610883 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term350 A s a t) (h2 : term635 A s a) : term689 A s a t.
Proof. exact (EQ_MP (@lem4609746 A s a t) (@lem4610882 A t s a h1 h2)). Qed.
Lemma lem4610884 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term635 A s a) : term690 A s a t.
Proof. exact (fun h0 : term350 A s a t => @lem4610883 A t s a h0 h1). Qed.
Lemma lem4610885 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term691 A s a t.
Proof. exact (fun h0 : term635 A s a => @lem4610884 A t s a h0). Qed.
Lemma lem4610890 {A : Type'} (a : A) (t : A -> Prop) : term701 A a t.
Proof. exact (fun s : A -> Prop => @lem4610885 A s a t). Qed.
Lemma lem4610895 {A : Type'} (t : A -> Prop) : term705 A t.
Proof. exact (fun a : A => @lem4610890 A a t). Qed.
Lemma lem4610900 {A : Type'} : term709 A.
Proof. exact (fun t : A -> Prop => @lem4610895 A t). Qed.
Lemma lem4610901 {A : Type'} : term708 A.
Proof. exact (EQ_MP (@lem4609740 A) (@lem4610900 A)). Qed.
Lemma lem4610902 {A : Type'} (t : A -> Prop) : term951 A t.
Proof. exact (@lem4610901 A t). Qed.
Lemma lem4610903 {A : Type'} (t : A -> Prop) : (term951 A t) = (term704 A t).
Proof. exact (eq_refl (term951 A t)). Qed.
Lemma lem4610904 {A : Type'} (t : A -> Prop) : term704 A t.
Proof. exact (EQ_MP (@lem4610903 A t) (@lem4610902 A t)). Qed.
Lemma lem4610905 {A : Type'} (t : A -> Prop) (a : A) : term952 A t a.
Proof. exact (@lem4610904 A t a). Qed.
Lemma lem4610906 {A : Type'} (a : A) (t : A -> Prop) : (term952 A t a) = (term700 A a t).
Proof. exact (eq_refl (term952 A t a)). Qed.
Lemma lem4610907 {A : Type'} (a : A) (t : A -> Prop) : term700 A a t.
Proof. exact (EQ_MP (@lem4610906 A a t) (@lem4610905 A t a)). Qed.
Lemma lem4610908 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) : term953 A a t s.
Proof. exact (@lem4610907 A a t s). Qed.
Lemma lem4610909 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term953 A a t s) = (term692 A s a t).
Proof. exact (eq_refl (term953 A a t s)). Qed.
Lemma lem4610910 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term692 A s a t.
Proof. exact (EQ_MP (@lem4610909 A s a t) (@lem4610908 A a t s)). Qed.
Lemma lem4610912 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term692 A s a t.
Proof. exact (@lem4609475 A s a t (@lem4610910 A s a t)). Qed.
Lemma lem4610913 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term693 A s a t) : False.
Proof. exact (@lem4610912 A s a t (@lem4609459 A s a t h1)). Qed.
Lemma lem4610914 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term693 A s a t) : (term693 A s a t) = False.
Proof. exact (prop_ext (fun h2 : term693 A s a t => @lem4610913 A s a t h1) (fun h2 : False => @lem4609459 A s a t h1)). Qed.
Lemma lem4610915 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term693 A s a t) : False.
Proof. exact (EQ_MP (@lem4610914 A s a t h1) (@lem4609459 A s a t h1)). Qed.
Lemma lem4610916 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term692 A s a t.
Proof. exact (fun h0 : term693 A s a t => @lem4610915 A s a t h0). Qed.
Lemma lem4610917 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term691 A s a t.
Proof. exact (EQ_MP (@lem4609458 A s a t) (@lem4610916 A s a t)). Qed.
Lemma lem4610918 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term676 A s a t.
Proof. exact (EQ_MP (@lem4609454 A s a t) (@lem4610917 A s a t)). Qed.
Lemma lem4610919 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term675 A s a t.
Proof. exact (EQ_MP (@lem4609276 A s a t) (@lem4610918 A s a t)). Qed.
Lemma lem4610920 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term2 A a s) : term292 A s a t.
Proof. exact (@lem4610919 A s a t (@lem4606462 A a s h1)). Qed.
Lemma lem4610921 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term62 A s a t) : term62 A s a t.
Proof. exact (h1). Qed.
Lemma lem4610922 (t1 : Prop) : term657 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4610923 (t1 : Prop) : (term657 t1) = (term658 t1).
Proof. exact (eq_refl (term657 t1)). Qed.
Lemma lem4610924 (t1 : Prop) : term658 t1.
Proof. exact (EQ_MP (@lem4610923 t1) (@lem4610922 t1)). Qed.
Lemma lem4610925 (t1 : Prop) (t2 : Prop) : term659 t1 t2.
Proof. exact (@lem4610924 t1 t2). Qed.
Lemma lem4610926 (t1 : Prop) (t2 : Prop) : (term659 t1 t2) = (term660 t1 t2).
Proof. exact (eq_refl (term659 t1 t2)). Qed.
Lemma lem4610927 (t1 : Prop) (t2 : Prop) : term660 t1 t2.
Proof. exact (EQ_MP (@lem4610926 t1 t2) (@lem4610925 t1 t2)). Qed.
Lemma lem4610928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term661 t1 t2 t3.
Proof. exact (@lem4610927 t1 t2 t3). Qed.
Lemma lem4610929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term661 t1 t2 t3) = ((term662 t1 t2 t3) = (term663 t1 t2 t3)).
Proof. exact (eq_refl (term661 t1 t2 t3)). Qed.
Lemma lem4610930 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term662 t1 t2 t3) = (term663 t1 t2 t3).
Proof. exact (EQ_MP (@lem4610929 t1 t2 t3) (@lem4610928 t1 t2 t3)). Qed.
Lemma lem4610931 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term663 t1 t2 t3) = (term662 t1 t2 t3).
Proof. exact (SYM (@lem4610930 t1 t2 t3)). Qed.
Lemma lem4610932 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : term954 A t a s.
Proof. exact (conj (@lem4610921 A s a t h2) (@lem4606461 A a s h1)). Qed.
Lemma lem4610938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4610939 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4610938 A s t). Qed.
Lemma lem4610940 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term62 A s a t) = (term319 A s a t).
Proof. exact (@lem4610939 A (@DELETE A s a) t). Qed.
Lemma lem4610947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610948 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term955 A s a t) = (term956 A s a t).
Proof. exact (MK_COMB (@lem4610947) (@lem4610940 A s a t)). Qed.
Lemma lem4610949 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = (@IN A a s).
Proof. exact (eq_refl (@IN A a s)). Qed.
Lemma lem4610950 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term954 A t a s) = (term957 A t a s).
Proof. exact (MK_COMB (@lem4610948 A s a t) (@lem4610949 A a s)). Qed.
Lemma lem4610953 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4610954 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term958 A t a s) = (term959 A t a s).
Proof. exact (MK_COMB (@lem4610953) (@lem4610950 A t a s)). Qed.
Lemma lem4610960 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term666 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4610961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term666 A s t).
Proof. exact (@lem4610960 A s t). Qed.
Lemma lem4610962 {A : Type'} (s : A -> Prop) (a : A) : (s = (term960 A s a)) = (term961 A s a).
Proof. exact (@lem4610961 A s (term960 A s a)). Qed.
Lemma lem4610971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4610972 {A : Type'} (s : A -> Prop) (a : A) : (term962 A s a) = (term963 A s a).
Proof. exact (MK_COMB (@lem4610971) (@lem4610962 A s a)). Qed.
Lemma lem4610974 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4610975 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term36 A s t).
Proof. exact (@lem4610974 A s t). Qed.
Lemma lem4610976 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term62 A s a t) = (term319 A s a t).
Proof. exact (@lem4610975 A (@DELETE A s a) t). Qed.
Lemma lem4610983 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term964 A s a t) = (term965 A s a t).
Proof. exact (MK_COMB (@lem4610972 A s a) (@lem4610976 A s a t)). Qed.
Lemma lem4610986 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term966 A s a t) = (term967 A s a t).
Proof. exact (MK_COMB (@lem4610954 A t a s) (@lem4610983 A s a t)). Qed.
Lemma lem4610989 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term967 A s a t) = (term966 A s a t).
Proof. exact (SYM (@lem4610986 A s a t)). Qed.
Lemma lem4611001 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4611002 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4611001 A s x y). Qed.
Lemma lem4611003 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term339 A s x a).
Proof. exact (@lem4611002 A s x a). Qed.
Lemma lem4611007 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611008 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611007 A P x). Qed.
Lemma lem4611009 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4611008 A s x). Qed.
Lemma lem4611010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611011 {A : Type'} (s : A -> Prop) (x : A) : (term340 A x s) = (term341 A s x).
Proof. exact (MK_COMB (@lem4611010) (@lem4611009 A s x)). Qed.
Lemma lem4611014 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4611015 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term339 A s x a) = (term343 A s x a).
Proof. exact (MK_COMB (@lem4611011 A s x) (@lem4611014 A x a)). Qed.
Lemma lem4611018 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term343 A s x a).
Proof. exact (TRANS (@lem4611003 A s x a) (@lem4611015 A s x a)). Qed.
Lemma lem4611019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4611020 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term344 A x s a) = (term345 A s x a).
Proof. exact (MK_COMB (@lem4611019) (@lem4611018 A s x a)). Qed.
Lemma lem4611022 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611023 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611022 A P x). Qed.
Lemma lem4611024 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4611023 A t x). Qed.
Lemma lem4611025 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term346 A s a x t) = (term347 A s a t x).
Proof. exact (MK_COMB (@lem4611020 A s x a) (@lem4611024 A t x)). Qed.
Lemma lem4611028 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term348 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611025 A s a t x)). Qed.
Lemma lem4611029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611030 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term319 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4611029 A) (@lem4611028 A s a t)). Qed.
Lemma lem4611035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611036 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term956 A s a t) = (term968 A s a t).
Proof. exact (MK_COMB (@lem4611035) (@lem4611030 A s a t)). Qed.
Lemma lem4611038 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611039 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611038 A P x). Qed.
Lemma lem4611040 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem4611039 A s a). Qed.
Lemma lem4611041 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term957 A t a s) = (term969 A t s a).
Proof. exact (MK_COMB (@lem4611036 A s a t) (@lem4611040 A s a)). Qed.
Lemma lem4611044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4611045 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term959 A t a s) = (term970 A t s a).
Proof. exact (MK_COMB (@lem4611044) (@lem4611041 A t s a)). Qed.
Lemma lem4611055 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611055 A P x). Qed.
Lemma lem4611057 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4611056 A s x). Qed.
Lemma lem4611058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4611059 {A : Type'} (s : A -> Prop) (x : A) : (term680 A x s) = (term681 A s x).
Proof. exact (MK_COMB (@lem4611058) (@lem4611057 A s x)). Qed.
Lemma lem4611061 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4611062 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term357 A x y s) = (term358 A y x s).
Proof. exact (@lem4611061 A y x s). Qed.
Lemma lem4611063 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term971 A x s a) = (term972 A x s a).
Proof. exact (@lem4611062 A a x (@DELETE A s a)). Qed.
Lemma lem4611069 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4611070 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4611069 A s x y). Qed.
Lemma lem4611071 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term339 A s x a).
Proof. exact (@lem4611070 A s x a). Qed.
Lemma lem4611075 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611076 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611075 A P x). Qed.
Lemma lem4611077 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4611076 A s x). Qed.
Lemma lem4611078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611079 {A : Type'} (s : A -> Prop) (x : A) : (term340 A x s) = (term341 A s x).
Proof. exact (MK_COMB (@lem4611078) (@lem4611077 A s x)). Qed.
Lemma lem4611082 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4611083 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term339 A s x a) = (term343 A s x a).
Proof. exact (MK_COMB (@lem4611079 A s x) (@lem4611082 A x a)). Qed.
Lemma lem4611086 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term343 A s x a).
Proof. exact (TRANS (@lem4611071 A s x a) (@lem4611083 A s x a)). Qed.
Lemma lem4611087 {A : Type'} (x : A) (a : A) : (term359 A x a) = (term359 A x a).
Proof. exact (eq_refl (term359 A x a)). Qed.
Lemma lem4611088 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term972 A x s a) = (term973 A s x a).
Proof. exact (MK_COMB (@lem4611087 A x a) (@lem4611086 A s x a)). Qed.
Lemma lem4611091 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term971 A x s a) = (term973 A s x a).
Proof. exact (TRANS (@lem4611063 A x s a) (@lem4611088 A s x a)). Qed.
Lemma lem4611092 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((@IN A x s) = (term971 A x s a)) = ((s x) = (term973 A s x a)).
Proof. exact (MK_COMB (@lem4611059 A s x) (@lem4611091 A s x a)). Qed.
Lemma lem4611095 {A : Type'} (s : A -> Prop) (a : A) : (term974 A s a) = (term975 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611092 A s x a)). Qed.
Lemma lem4611096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611097 {A : Type'} (s : A -> Prop) (a : A) : (term961 A s a) = (term976 A s a).
Proof. exact (MK_COMB (@lem4611096 A) (@lem4611095 A s a)). Qed.
Lemma lem4611102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611103 {A : Type'} (s : A -> Prop) (a : A) : (term963 A s a) = (term977 A s a).
Proof. exact (MK_COMB (@lem4611102) (@lem4611097 A s a)). Qed.
Lemma lem4611111 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem4611112 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term338 A x s y) = (term339 A s x y).
Proof. exact (@lem4611111 A s x y). Qed.
Lemma lem4611113 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term339 A s x a).
Proof. exact (@lem4611112 A s x a). Qed.
Lemma lem4611117 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611118 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611117 A P x). Qed.
Lemma lem4611119 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4611118 A s x). Qed.
Lemma lem4611120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611121 {A : Type'} (s : A -> Prop) (x : A) : (term340 A x s) = (term341 A s x).
Proof. exact (MK_COMB (@lem4611120) (@lem4611119 A s x)). Qed.
Lemma lem4611124 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term342 A x a).
Proof. exact (eq_refl (term342 A x a)). Qed.
Lemma lem4611125 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term339 A s x a) = (term343 A s x a).
Proof. exact (MK_COMB (@lem4611121 A s x) (@lem4611124 A x a)). Qed.
Lemma lem4611128 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term338 A x s a) = (term343 A s x a).
Proof. exact (TRANS (@lem4611113 A s x a) (@lem4611125 A s x a)). Qed.
Lemma lem4611129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4611130 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term344 A x s a) = (term345 A s x a).
Proof. exact (MK_COMB (@lem4611129) (@lem4611128 A s x a)). Qed.
Lemma lem4611132 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4611133 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4611132 A P x). Qed.
Lemma lem4611134 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4611133 A t x). Qed.
Lemma lem4611135 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term346 A s a x t) = (term347 A s a t x).
Proof. exact (MK_COMB (@lem4611130 A s x a) (@lem4611134 A t x)). Qed.
Lemma lem4611138 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term348 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611135 A s a t x)). Qed.
Lemma lem4611139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611140 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term319 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4611139 A) (@lem4611138 A s a t)). Qed.
Lemma lem4611145 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term965 A s a t) = (term978 A s a t).
Proof. exact (MK_COMB (@lem4611103 A s a) (@lem4611140 A s a t)). Qed.
Lemma lem4611148 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term967 A s a t) = (term979 A s a t).
Proof. exact (MK_COMB (@lem4611045 A t s a) (@lem4611145 A s a t)). Qed.
Lemma lem4611151 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term979 A s a t) = (term967 A s a t).
Proof. exact (SYM (@lem4611148 A s a t)). Qed.
Lemma lem4611153 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4611154 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term979 A s a t) = (term980 A s a t).
Proof. exact (@lem4611153 (term979 A s a t)). Qed.
Lemma lem4611155 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term980 A s a t) = (term979 A s a t).
Proof. exact (SYM (@lem4611154 A s a t)). Qed.
Lemma lem4611156 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term981 A s a t) : term981 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611159 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term980 A s a t) : term980 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611160 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term982 A s a t.
Proof. exact (fun h0 : term980 A s a t => @lem4611159 A s a t h0). Qed.
Lemma lem4611161 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term982 A s a t) : term982 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611162 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term980 A s a t) : term980 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611163 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term980 A s a t) (h2 : term982 A s a t) : term980 A s a t.
Proof. exact (@lem4611161 A s a t h2 (@lem4611162 A s a t h1)). Qed.
Lemma lem4611164 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term980 A s a t) : term983 A s a t.
Proof. exact (fun h0 : term982 A s a t => @lem4611163 A s a t h1 h0). Qed.
Lemma lem4611165 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term982 A s a t) : term982 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611166 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term980 A s a t) (h2 : term982 A s a t) : term980 A s a t.
Proof. exact (@lem4611164 A s a t h1 (@lem4611165 A s a t h2)). Qed.
Lemma lem4611167 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term982 A s a t) : term982 A s a t.
Proof. exact (fun h0 : term980 A s a t => @lem4611166 A s a t h0 h1). Qed.
Lemma lem4611168 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term984 A s a t.
Proof. exact (fun h0 : term982 A s a t => @lem4611167 A s a t h0). Qed.
Lemma lem4611171 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term982 A s a t.
Proof. exact (@lem4611168 A s a t (@lem4611160 A s a t)). Qed.
Lemma lem4611172 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term982 A s a t.
Proof. exact (@lem4611171 A s a t). Qed.
Lemma lem4611186 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4611187 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term980 A s a t) = (term985 A s a t).
Proof. exact (@lem4611186 (term981 A s a t)). Qed.
Lemma lem4611189 (t : Prop) : (term382 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4611190 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term985 A s a t) = (term979 A s a t).
Proof. exact (@lem4611189 (term979 A s a t)). Qed.
Lemma lem4611193 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term980 A s a t) = (term979 A s a t).
Proof. exact (TRANS (@lem4611187 A s a t) (@lem4611190 A s a t)). Qed.
Lemma lem4611222 {A : Type'} (a : A) (t : A -> Prop) : (term986 A a t) = (term987 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4611193 A s a t)). Qed.
Lemma lem4611223 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4611224 {A : Type'} (a : A) (t : A -> Prop) : (term988 A a t) = (term989 A a t).
Proof. exact (MK_COMB (@lem4611223 A) (@lem4611222 A a t)). Qed.
Lemma lem4611229 {A : Type'} (t : A -> Prop) : (term990 A t) = (term991 A t).
Proof. exact (fun_ext (fun a : A => @lem4611224 A a t)). Qed.
Lemma lem4611230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611231 {A : Type'} (t : A -> Prop) : (term992 A t) = (term993 A t).
Proof. exact (MK_COMB (@lem4611230 A) (@lem4611229 A t)). Qed.
Lemma lem4611236 {A : Type'} : (term994 A) = (term995 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4611231 A t)). Qed.
Lemma lem4611237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4611246 {A : Type'} : (term996 A) = (term997 A).
Proof. exact (MK_COMB (@lem4611237 A) (@lem4611236 A)). Qed.
Lemma lem4611257 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term347 A s a t x)). Qed.
Lemma lem4611258 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611257 A s a t x)). Qed.
Lemma lem4611259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611260 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4611259 A) (@lem4611258 A s a t)). Qed.
Lemma lem4611275 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (term973 A s x a)) = ((s x) = (term973 A s x a)).
Proof. exact (eq_refl ((s x) = (term973 A s x a))). Qed.
Lemma lem4611276 {A : Type'} (s : A -> Prop) (a : A) : (term975 A s a) = (term975 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611275 A s x a)). Qed.
Lemma lem4611277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611278 {A : Type'} (s : A -> Prop) (a : A) : (term976 A s a) = (term976 A s a).
Proof. exact (MK_COMB (@lem4611277 A) (@lem4611276 A s a)). Qed.
Lemma lem4611279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611280 {A : Type'} (s : A -> Prop) (a : A) : (term977 A s a) = (term977 A s a).
Proof. exact (MK_COMB (@lem4611279) (@lem4611278 A s a)). Qed.
Lemma lem4611281 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term978 A s a t) = (term978 A s a t).
Proof. exact (MK_COMB (@lem4611280 A s a) (@lem4611260 A s a t)). Qed.
Lemma lem4611282 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem4611293 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term347 A s a t x)). Qed.
Lemma lem4611294 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term349 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611293 A s a t x)). Qed.
Lemma lem4611295 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611296 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term350 A s a t).
Proof. exact (MK_COMB (@lem4611295 A) (@lem4611294 A s a t)). Qed.
Lemma lem4611297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611298 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term968 A s a t) = (term968 A s a t).
Proof. exact (MK_COMB (@lem4611297) (@lem4611296 A s a t)). Qed.
Lemma lem4611299 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term969 A t s a) = (term969 A t s a).
Proof. exact (MK_COMB (@lem4611298 A s a t) (@lem4611282 A s a)). Qed.
Lemma lem4611300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4611301 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term970 A t s a) = (term970 A t s a).
Proof. exact (MK_COMB (@lem4611300) (@lem4611299 A t s a)). Qed.
Lemma lem4611302 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term979 A s a t) = (term979 A s a t).
Proof. exact (MK_COMB (@lem4611301 A t s a) (@lem4611281 A s a t)). Qed.
Lemma lem4611303 {A : Type'} (a : A) (t : A -> Prop) : (term987 A a t) = (term987 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4611302 A s a t)). Qed.
Lemma lem4611304 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4611305 {A : Type'} (a : A) (t : A -> Prop) : (term989 A a t) = (term989 A a t).
Proof. exact (MK_COMB (@lem4611304 A) (@lem4611303 A a t)). Qed.
Lemma lem4611306 {A : Type'} (t : A -> Prop) : (term991 A t) = (term991 A t).
Proof. exact (fun_ext (fun a : A => @lem4611305 A a t)). Qed.
Lemma lem4611307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611308 {A : Type'} (t : A -> Prop) : (term993 A t) = (term993 A t).
Proof. exact (MK_COMB (@lem4611307 A) (@lem4611306 A t)). Qed.
Lemma lem4611309 {A : Type'} : (term995 A) = (term995 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4611308 A t)). Qed.
Lemma lem4611310 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4611311 {A : Type'} : (term997 A) = (term997 A).
Proof. exact (MK_COMB (@lem4611310 A) (@lem4611309 A)). Qed.
Lemma lem4611368 {A : Type'} : (term996 A) = (term997 A).
Proof. exact (TRANS (@lem4611246 A) (@lem4611311 A)). Qed.
Lemma lem4611369 {A : Type'} : (term997 A) = (term996 A).
Proof. exact (SYM (@lem4611368 A)). Qed.
Lemma lem4611370 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term969 A t s a.
Proof. exact (h1). Qed.
Lemma lem4611372 (p : Prop) : p = (term375 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4611373 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term978 A s a t) = (term998 A s a t).
Proof. exact (@lem4611372 (term978 A s a t)). Qed.
Lemma lem4611374 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term998 A s a t) = (term978 A s a t).
Proof. exact (SYM (@lem4611373 A s a t)). Qed.
Lemma lem4611375 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term999 A s a t) : term999 A s a t.
Proof. exact (h1). Qed.
Lemma lem4611379 {A : Type'} (x : A) (a : A) : (term712 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem4611381 {A : Type'} (s : A -> Prop) (x : A) : (term713 A s x) = (term713 A s x).
Proof. exact (eq_refl (term713 A s x)). Qed.
Lemma lem4611382 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term714 A s x a) = (term715 A s x a).
Proof. exact (MK_COMB (@lem4611381 A s x) (@lem4611379 A x a)). Qed.
Lemma lem4611383 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term714 A s x a).
Proof. exact (@lem17045 (s x) (term342 A x a)). Qed.
Lemma lem4611384 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term715 A s x a).
Proof. exact (TRANS (@lem4611383 A s x a) (@lem4611382 A s x a)). Qed.
Lemma lem4611385 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4611386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611387 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term717 A s x a) = (term718 A s x a).
Proof. exact (MK_COMB (@lem4611386) (@lem4611384 A s x a)). Qed.
Lemma lem4611388 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term719 A s a t x) = (term720 A s a t x).
Proof. exact (MK_COMB (@lem4611387 A s x a) (@lem4611385 A t x)). Qed.
Lemma lem4611389 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term719 A s a t x).
Proof. exact (@lem17265 (term343 A s x a) (t x)). Qed.
Lemma lem4611390 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term347 A s a t x) = (term720 A s a t x).
Proof. exact (TRANS (@lem4611389 A s a t x) (@lem4611388 A s a t x)). Qed.
Lemma lem4611391 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term349 A s a t) = (term721 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611390 A s a t x)). Qed.
Lemma lem4611392 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611393 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term350 A s a t) = (term722 A s a t).
Proof. exact (MK_COMB (@lem4611392 A) (@lem4611391 A s a t)). Qed.
Lemma lem4611394 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem4611395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611396 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term968 A s a t) = (term1000 A s a t).
Proof. exact (MK_COMB (@lem4611395) (@lem4611393 A s a t)). Qed.
Lemma lem4611433 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term969 A t s a) = (term1001 A t s a).
Proof. exact (MK_COMB (@lem4611396 A s a t) (@lem4611394 A s a)). Qed.
Lemma lem4611434 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1001 A t s a.
Proof. exact (EQ_MP (@lem4611433 A t s a) (@lem4611370 A t s a h1)). Qed.
Lemma lem4611444 {A : Type'} (x : A) (a : A) : (term712 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem4611446 {A : Type'} (s : A -> Prop) (x : A) : (term713 A s x) = (term713 A s x).
Proof. exact (eq_refl (term713 A s x)). Qed.
Lemma lem4611447 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term714 A s x a) = (term715 A s x a).
Proof. exact (MK_COMB (@lem4611446 A s x) (@lem4611444 A x a)). Qed.
Lemma lem4611448 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term714 A s x a).
Proof. exact (@lem17045 (s x) (term342 A x a)). Qed.
Lemma lem4611449 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term716 A s x a) = (term715 A s x a).
Proof. exact (TRANS (@lem4611448 A s x a) (@lem4611447 A s x a)). Qed.
Lemma lem4611454 {A : Type'} (x : A) (a : A) : (term1002 A x a) = (term1002 A x a).
Proof. exact (eq_refl (term1002 A x a)). Qed.
Lemma lem4611455 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1003 A s x a) = (term1004 A s x a).
Proof. exact (MK_COMB (@lem4611454 A x a) (@lem4611449 A s x a)). Qed.
Lemma lem4611456 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1005 A s x a) = (term1003 A s x a).
Proof. exact (@lem17160 (x = a) (term343 A s x a)). Qed.
Lemma lem4611457 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1005 A s x a) = (term1004 A s x a).
Proof. exact (TRANS (@lem4611456 A s x a) (@lem4611455 A s x a)). Qed.
Lemma lem4611463 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1006 A s x a) = (term1006 A s x a).
Proof. exact (eq_refl (term1006 A s x a)). Qed.
Lemma lem4611465 {A : Type'} (s : A -> Prop) (x : A) : (term341 A s x) = (term341 A s x).
Proof. exact (eq_refl (term341 A s x)). Qed.
Lemma lem4611466 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1007 A s x a) = (term1008 A s x a).
Proof. exact (MK_COMB (@lem4611465 A s x) (@lem4611457 A s x a)). Qed.
Lemma lem4611467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611468 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1009 A s x a) = (term1010 A s x a).
Proof. exact (MK_COMB (@lem4611467) (@lem4611466 A s x a)). Qed.
Lemma lem4611469 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1011 A s x a) = (term1012 A s x a).
Proof. exact (MK_COMB (@lem4611468 A s x a) (@lem4611463 A s x a)). Qed.
Lemma lem4611470 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1013 A s x a) = (term1011 A s x a).
Proof. exact (@lem17646 (s x) (term973 A s x a)). Qed.
Lemma lem4611471 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1013 A s x a) = (term1012 A s x a).
Proof. exact (TRANS (@lem4611470 A s x a) (@lem4611469 A s x a)). Qed.
Lemma lem4611472 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4611473 {A : Type'} (s : A -> Prop) (a : A) : (term1014 A s a) = (term1015 A s a).
Proof. exact (@lem4611472 A (term975 A s a)). Qed.
Lemma lem4611474 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1016 A s a x) = ((s x) = (term973 A s x a)).
Proof. exact (eq_refl (term1016 A s a x)). Qed.
Lemma lem4611475 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4611476 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1017 A s a x) = (term1013 A s x a).
Proof. exact (MK_COMB (@lem4611475) (@lem4611474 A s x a)). Qed.
Lemma lem4611477 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1017 A s a x) = (term1012 A s x a).
Proof. exact (TRANS (@lem4611476 A s x a) (@lem4611471 A s x a)). Qed.
Lemma lem4611478 {A : Type'} (s : A -> Prop) (a : A) : (term1018 A s a) = (term1019 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611477 A s x a)). Qed.
Lemma lem4611479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611480 {A : Type'} (s : A -> Prop) (a : A) : (term1015 A s a) = (term1020 A s a).
Proof. exact (MK_COMB (@lem4611479 A) (@lem4611478 A s a)). Qed.
Lemma lem4611481 {A : Type'} (s : A -> Prop) (a : A) : (term1014 A s a) = (term1020 A s a).
Proof. exact (TRANS (@lem4611473 A s a) (@lem4611480 A s a)). Qed.
Lemma lem4611492 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term440 A s a t x) = (term441 A s a t x).
Proof. exact (@lem17362 (term343 A s x a) (t x)). Qed.
Lemma lem4611493 {A : Type'} (P : A -> Prop) : (term442 A P) = (term443 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4611494 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term444 A s a t) = (term445 A s a t).
Proof. exact (@lem4611493 A (term349 A s a t)). Qed.
Lemma lem4611495 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term446 A s a t x) = (term347 A s a t x).
Proof. exact (eq_refl (term446 A s a t x)). Qed.
Lemma lem4611496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4611497 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term447 A s a t x) = (term440 A s a t x).
Proof. exact (MK_COMB (@lem4611496) (@lem4611495 A s a t x)). Qed.
Lemma lem4611498 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term447 A s a t x) = (term441 A s a t x).
Proof. exact (TRANS (@lem4611497 A s a t x) (@lem4611492 A s a t x)). Qed.
Lemma lem4611499 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term448 A s a t) = (term449 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611498 A s a t x)). Qed.
Lemma lem4611500 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611501 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term445 A s a t) = (term450 A s a t).
Proof. exact (MK_COMB (@lem4611500 A) (@lem4611499 A s a t)). Qed.
Lemma lem4611502 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term444 A s a t) = (term450 A s a t).
Proof. exact (TRANS (@lem4611494 A s a t) (@lem4611501 A s a t)). Qed.
Lemma lem4611503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611504 {A : Type'} (s : A -> Prop) (a : A) : (term1021 A s a) = (term1022 A s a).
Proof. exact (MK_COMB (@lem4611503) (@lem4611481 A s a)). Qed.
Lemma lem4611505 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1023 A s a t) = (term1024 A s a t).
Proof. exact (MK_COMB (@lem4611504 A s a) (@lem4611502 A s a t)). Qed.
Lemma lem4611506 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term999 A s a t) = (term1023 A s a t).
Proof. exact (@lem17045 (term976 A s a) (term350 A s a t)). Qed.
Lemma lem4611507 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term999 A s a t) = (term1024 A s a t).
Proof. exact (TRANS (@lem4611506 A s a t) (@lem4611505 A s a t)). Qed.
Lemma lem4611509 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term552 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4611510 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term552 A P Q).
Proof. exact (@lem4611509 A P Q). Qed.
Lemma lem4611511 {A : Type'} (s : A -> Prop) (a : A) : (term1025 A s a) = (term1026 A s a).
Proof. exact (@lem4611510 A (term1027 A s a) (term1028 A s a)). Qed.
Lemma lem4611512 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1029 A s a x) = (term1008 A s x a).
Proof. exact (eq_refl (term1029 A s a x)). Qed.
Lemma lem4611513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611514 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1030 A s a x) = (term1010 A s x a).
Proof. exact (MK_COMB (@lem4611513) (@lem4611512 A s x a)). Qed.
Lemma lem4611515 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1031 A s a x) = (term1006 A s x a).
Proof. exact (eq_refl (term1031 A s a x)). Qed.
Lemma lem4611516 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1032 A s a x) = (term1012 A s x a).
Proof. exact (MK_COMB (@lem4611514 A s x a) (@lem4611515 A s x a)). Qed.
Lemma lem4611517 {A : Type'} (s : A -> Prop) (a : A) : (term1033 A s a) = (term1019 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611516 A s x a)). Qed.
Lemma lem4611518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611519 {A : Type'} (s : A -> Prop) (a : A) : (term1025 A s a) = (term1020 A s a).
Proof. exact (MK_COMB (@lem4611518 A) (@lem4611517 A s a)). Qed.
Lemma lem4611520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4611521 {A : Type'} (s : A -> Prop) (a : A) : (term1034 A s a) = (term1035 A s a).
Proof. exact (MK_COMB (@lem4611520) (@lem4611519 A s a)). Qed.
Lemma lem4611522 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1029 A s a x) = (term1008 A s x a).
Proof. exact (eq_refl (term1029 A s a x)). Qed.
Lemma lem4611523 {A : Type'} (s : A -> Prop) (a : A) : (term1036 A s a) = (term1027 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611522 A s x a)). Qed.
Lemma lem4611524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611525 {A : Type'} (s : A -> Prop) (a : A) : (term1037 A s a) = (term1038 A s a).
Proof. exact (MK_COMB (@lem4611524 A) (@lem4611523 A s a)). Qed.
Lemma lem4611526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611527 {A : Type'} (s : A -> Prop) (a : A) : (term1039 A s a) = (term1040 A s a).
Proof. exact (MK_COMB (@lem4611526) (@lem4611525 A s a)). Qed.
Lemma lem4611528 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1031 A s a x) = (term1006 A s x a).
Proof. exact (eq_refl (term1031 A s a x)). Qed.
Lemma lem4611529 {A : Type'} (s : A -> Prop) (a : A) : (term1041 A s a) = (term1028 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611528 A s x a)). Qed.
Lemma lem4611530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611531 {A : Type'} (s : A -> Prop) (a : A) : (term1042 A s a) = (term1043 A s a).
Proof. exact (MK_COMB (@lem4611530 A) (@lem4611529 A s a)). Qed.
Lemma lem4611532 {A : Type'} (s : A -> Prop) (a : A) : (term1026 A s a) = (term1044 A s a).
Proof. exact (MK_COMB (@lem4611527 A s a) (@lem4611531 A s a)). Qed.
Lemma lem4611533 {A : Type'} (s : A -> Prop) (a : A) : ((term1025 A s a) = (term1026 A s a)) = ((term1020 A s a) = (term1044 A s a)).
Proof. exact (MK_COMB (@lem4611521 A s a) (@lem4611532 A s a)). Qed.
Lemma lem4611534 {A : Type'} (s : A -> Prop) (a : A) : (term1020 A s a) = (term1044 A s a).
Proof. exact (EQ_MP (@lem4611533 A s a) (@lem4611511 A s a)). Qed.
Lemma lem4611611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611612 {A : Type'} (s : A -> Prop) (a : A) : (term1022 A s a) = (term1045 A s a).
Proof. exact (MK_COMB (@lem4611611) (@lem4611534 A s a)). Qed.
Lemma lem4611661 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term450 A s a t) = (term450 A s a t).
Proof. exact (eq_refl (term450 A s a t)). Qed.
Lemma lem4611662 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1024 A s a t) = (term1046 A s a t).
Proof. exact (MK_COMB (@lem4611612 A s a) (@lem4611661 A s a t)). Qed.
Lemma lem4611664 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4611665 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (@lem4611664 A P Q). Qed.
Lemma lem4611666 {A : Type'} (s : A -> Prop) (a : A) : (term1026 A s a) = (term1025 A s a).
Proof. exact (@lem4611665 A (term1027 A s a) (term1028 A s a)). Qed.
Lemma lem4611667 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1029 A s a x) = (term1008 A s x a).
Proof. exact (eq_refl (term1029 A s a x)). Qed.
Lemma lem4611668 {A : Type'} (s : A -> Prop) (a : A) : (term1036 A s a) = (term1027 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611667 A s x a)). Qed.
Lemma lem4611669 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611670 {A : Type'} (s : A -> Prop) (a : A) : (term1037 A s a) = (term1038 A s a).
Proof. exact (MK_COMB (@lem4611669 A) (@lem4611668 A s a)). Qed.
Lemma lem4611671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611672 {A : Type'} (s : A -> Prop) (a : A) : (term1039 A s a) = (term1040 A s a).
Proof. exact (MK_COMB (@lem4611671) (@lem4611670 A s a)). Qed.
Lemma lem4611673 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1031 A s a x) = (term1006 A s x a).
Proof. exact (eq_refl (term1031 A s a x)). Qed.
Lemma lem4611674 {A : Type'} (s : A -> Prop) (a : A) : (term1041 A s a) = (term1028 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611673 A s x a)). Qed.
Lemma lem4611675 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611676 {A : Type'} (s : A -> Prop) (a : A) : (term1042 A s a) = (term1043 A s a).
Proof. exact (MK_COMB (@lem4611675 A) (@lem4611674 A s a)). Qed.
Lemma lem4611677 {A : Type'} (s : A -> Prop) (a : A) : (term1026 A s a) = (term1044 A s a).
Proof. exact (MK_COMB (@lem4611672 A s a) (@lem4611676 A s a)). Qed.
Lemma lem4611678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4611679 {A : Type'} (s : A -> Prop) (a : A) : (term1047 A s a) = (term1048 A s a).
Proof. exact (MK_COMB (@lem4611678) (@lem4611677 A s a)). Qed.
Lemma lem4611680 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1029 A s a x) = (term1008 A s x a).
Proof. exact (eq_refl (term1029 A s a x)). Qed.
Lemma lem4611681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611682 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1030 A s a x) = (term1010 A s x a).
Proof. exact (MK_COMB (@lem4611681) (@lem4611680 A s x a)). Qed.
Lemma lem4611683 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1031 A s a x) = (term1006 A s x a).
Proof. exact (eq_refl (term1031 A s a x)). Qed.
Lemma lem4611684 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1032 A s a x) = (term1012 A s x a).
Proof. exact (MK_COMB (@lem4611682 A s x a) (@lem4611683 A s x a)). Qed.
Lemma lem4611685 {A : Type'} (s : A -> Prop) (a : A) : (term1033 A s a) = (term1019 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611684 A s x a)). Qed.
Lemma lem4611686 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611687 {A : Type'} (s : A -> Prop) (a : A) : (term1025 A s a) = (term1020 A s a).
Proof. exact (MK_COMB (@lem4611686 A) (@lem4611685 A s a)). Qed.
Lemma lem4611688 {A : Type'} (s : A -> Prop) (a : A) : ((term1026 A s a) = (term1025 A s a)) = ((term1044 A s a) = (term1020 A s a)).
Proof. exact (MK_COMB (@lem4611679 A s a) (@lem4611687 A s a)). Qed.
Lemma lem4611689 {A : Type'} (s : A -> Prop) (a : A) : (term1044 A s a) = (term1020 A s a).
Proof. exact (EQ_MP (@lem4611688 A s a) (@lem4611666 A s a)). Qed.
Lemma lem4611690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611691 {A : Type'} (s : A -> Prop) (a : A) : (term1045 A s a) = (term1022 A s a).
Proof. exact (MK_COMB (@lem4611690) (@lem4611689 A s a)). Qed.
Lemma lem4611692 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term450 A s a t) = (term450 A s a t).
Proof. exact (eq_refl (term450 A s a t)). Qed.
Lemma lem4611693 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1046 A s a t) = (term1024 A s a t).
Proof. exact (MK_COMB (@lem4611691 A s a) (@lem4611692 A s a t)). Qed.
Lemma lem4611695 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4611696 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term552 A P Q) = (term553 A P Q).
Proof. exact (@lem4611695 A P Q). Qed.
Lemma lem4611697 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1049 A s a t) = (term1050 A s a t).
Proof. exact (@lem4611696 A (term1019 A s a) (term449 A s a t)). Qed.
Lemma lem4611698 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1051 A s a x) = (term1012 A s x a).
Proof. exact (eq_refl (term1051 A s a x)). Qed.
Lemma lem4611699 {A : Type'} (s : A -> Prop) (a : A) : (term1052 A s a) = (term1019 A s a).
Proof. exact (fun_ext (fun x : A => @lem4611698 A s x a)). Qed.
Lemma lem4611700 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611701 {A : Type'} (s : A -> Prop) (a : A) : (term1053 A s a) = (term1020 A s a).
Proof. exact (MK_COMB (@lem4611700 A) (@lem4611699 A s a)). Qed.
Lemma lem4611702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611703 {A : Type'} (s : A -> Prop) (a : A) : (term1054 A s a) = (term1022 A s a).
Proof. exact (MK_COMB (@lem4611702) (@lem4611701 A s a)). Qed.
Lemma lem4611704 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term516 A s a t x) = (term441 A s a t x).
Proof. exact (eq_refl (term516 A s a t x)). Qed.
Lemma lem4611705 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term517 A s a t) = (term449 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611704 A s a t x)). Qed.
Lemma lem4611706 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611707 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term518 A s a t) = (term450 A s a t).
Proof. exact (MK_COMB (@lem4611706 A) (@lem4611705 A s a t)). Qed.
Lemma lem4611708 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1049 A s a t) = (term1024 A s a t).
Proof. exact (MK_COMB (@lem4611703 A s a) (@lem4611707 A s a t)). Qed.
Lemma lem4611709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4611710 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1055 A s a t) = (term1056 A s a t).
Proof. exact (MK_COMB (@lem4611709) (@lem4611708 A s a t)). Qed.
Lemma lem4611711 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1051 A s a x) = (term1012 A s x a).
Proof. exact (eq_refl (term1051 A s a x)). Qed.
Lemma lem4611712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4611713 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term1057 A s a x) = (term1058 A s x a).
Proof. exact (MK_COMB (@lem4611712) (@lem4611711 A s x a)). Qed.
Lemma lem4611714 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term516 A s a t x) = (term441 A s a t x).
Proof. exact (eq_refl (term516 A s a t x)). Qed.
Lemma lem4611715 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term1059 A s a t x) = (term1060 A s a t x).
Proof. exact (MK_COMB (@lem4611713 A s x a) (@lem4611714 A s a t x)). Qed.
Lemma lem4611716 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1061 A s a t) = (term1062 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611715 A s a t x)). Qed.
Lemma lem4611717 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4611718 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1050 A s a t) = (term1063 A s a t).
Proof. exact (MK_COMB (@lem4611717 A) (@lem4611716 A s a t)). Qed.
Lemma lem4611719 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : ((term1049 A s a t) = (term1050 A s a t)) = ((term1024 A s a t) = (term1063 A s a t)).
Proof. exact (MK_COMB (@lem4611710 A s a t) (@lem4611718 A s a t)). Qed.
Lemma lem4611720 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1024 A s a t) = (term1063 A s a t).
Proof. exact (EQ_MP (@lem4611719 A s a t) (@lem4611697 A s a t)). Qed.
Lemma lem4611721 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1046 A s a t) = (term1063 A s a t).
Proof. exact (TRANS (@lem4611693 A s a t) (@lem4611720 A s a t)). Qed.
Lemma lem4611722 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1024 A s a t) = (term1063 A s a t).
Proof. exact (TRANS (@lem4611662 A s a t) (@lem4611721 A s a t)). Qed.
Lemma lem4611723 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term999 A s a t) = (term1063 A s a t).
Proof. exact (TRANS (@lem4611507 A s a t) (@lem4611722 A s a t)). Qed.
Lemma lem4611724 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term999 A s a t) : term1063 A s a t.
Proof. exact (EQ_MP (@lem4611723 A s a t) (@lem4611375 A s a t h1)). Qed.
Lemma lem4611728 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (s a).
Proof. exact (eq_refl (s a)). Qed.
Lemma lem4611747 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term720 A s a t x) = (term720 A s a t x).
Proof. exact (eq_refl (term720 A s a t x)). Qed.
Lemma lem4611748 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term721 A s a t) = (term721 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4611747 A s a t x)). Qed.
Lemma lem4611749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4611750 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term722 A s a t) = (term722 A s a t).
Proof. exact (MK_COMB (@lem4611749 A) (@lem4611748 A s a t)). Qed.
Lemma lem4611751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4611752 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1000 A s a t) = (term1000 A s a t).
Proof. exact (MK_COMB (@lem4611751) (@lem4611750 A s a t)). Qed.
Lemma lem4611753 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term1001 A t s a) = (term1001 A t s a).
Proof. exact (MK_COMB (@lem4611752 A s a t) (@lem4611728 A s a)). Qed.
Lemma lem4611754 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1001 A t s a.
Proof. exact (EQ_MP (@lem4611753 A t s a) (@lem4611434 A t s a h1)). Qed.
Lemma lem4611840 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term1060 A s a t x) : term1060 A s a t x.
Proof. exact (h1). Qed.
Lemma lem4611842 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term722 A s a t.
Proof. exact (proj1 (@lem4611754 A t s a h1)). Qed.
Lemma lem4611843 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1012 A s x a) : term1012 A s x a.
Proof. exact (h1). Qed.
Lemma lem4611844 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term441 A s a t x.
Proof. exact (h1). Qed.
Lemma lem4611845 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : term1008 A s x a.
Proof. exact (h1). Qed.
Lemma lem4611846 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) : term1006 A s x a.
Proof. exact (h1). Qed.
Lemma lem4611847 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : term1004 A s x a.
Proof. exact (proj2 (@lem4611845 A s x a h1)). Qed.
Lemma lem4611849 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : term715 A s x a.
Proof. exact (proj2 (@lem4611847 A s x a h1)). Qed.
Lemma lem4611853 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) : term973 A s x a.
Proof. exact (proj2 (@lem4611846 A s x a h1)). Qed.
Lemma lem4611856 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term343 A s x a) : term343 A s x a.
Proof. exact (h1). Qed.
Lemma lem4611860 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term343 A s x a.
Proof. exact (proj1 (@lem4611844 A s a t x h1)). Qed.
Lemma lem4611897 {A : Type'} (s : A -> Prop) (x : A) (h1 : term635 A s x) : term635 A s x.
Proof. exact (h1). Qed.
Lemma lem4611932 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4611963 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4612012 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) : (term720 A s a t x) = (term720 A s a t x).
Proof. exact (eq_refl (term720 A s a t x)). Qed.
Lemma lem4612013 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term721 A s a t) = (term721 A s a t).
Proof. exact (fun_ext (fun x : A => @lem4612012 A s a t x)). Qed.
Lemma lem4612014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4612016 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term722 A s a t) = (term722 A s a t).
Proof. exact (MK_COMB (@lem4612014 A) (@lem4612013 A s a t)). Qed.
Lemma lem4612017 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term722 A s a t.
Proof. exact (EQ_MP (@lem4612016 A s a t) (@lem4611842 A t s a h1)). Qed.
Lemma lem4612046 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1064 A s a t _55398.
Proof. exact (@lem4612017 A t s a h1 _55398). Qed.
Lemma lem4612047 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55398 : A) : (term1064 A s a t _55398) = (term720 A s a t _55398).
Proof. exact (eq_refl (term1064 A s a t _55398)). Qed.
Lemma lem4612048 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term720 A s a t _55398.
Proof. exact (EQ_MP (@lem4612047 A s a t _55398) (@lem4612046 A _55398 t s a h1)). Qed.
Lemma lem4612068 {A : Type'} (s : A -> Prop) (x : A) (h1 : term635 A s x) : term635 A s x.
Proof. exact (h1). Qed.
Lemma lem4612086 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : term342 A x a.
Proof. exact (proj1 (@lem4611847 A s x a h1)). Qed.
Lemma lem4612088 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4612104 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) : term635 A s x.
Proof. exact (proj1 (@lem4611846 A s x a h1)). Qed.
Lemma lem4612106 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4612122 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) : term635 A s x.
Proof. exact (proj1 (@lem4611846 A s x a h1)). Qed.
Lemma lem4612137 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (_55398 : A) : (term720 A s a t _55398) = (term1065 A s a t _55398).
Proof. exact (@lem4610931 (term635 A s _55398) (_55398 = a) (t _55398)). Qed.
Lemma lem4612138 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1065 A s a t _55398.
Proof. exact (EQ_MP (@lem4612137 A s a t _55398) (@lem4612048 A _55398 t s a h1)). Qed.
Lemma lem4612146 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term342 A x a.
Proof. exact (proj2 (@lem4611860 A s a t x h1)). Qed.
Lemma lem4612202 {A : Type'} (a : A) : (term636 A a) = (term636 A a).
Proof. exact (eq_refl (term636 A a)). Qed.
Lemma lem4612203 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term637 A a x) = (term638 A a).
Proof. exact (MK_COMB (@lem4612202 A a) (@lem4612088 A x a h1)). Qed.
Lemma lem4612204 {A : Type'} (a : A) : (term638 A a) = (term639 A a).
Proof. exact (eq_refl (term638 A a)). Qed.
Lemma lem4612205 {A : Type'} (a : A) (x : A) : (term640 A a x) = (term640 A a x).
Proof. exact (eq_refl (term640 A a x)). Qed.
Lemma lem4612206 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term638 A a)) = ((term637 A a x) = (term639 A a)).
Proof. exact (MK_COMB (@lem4612205 A a x) (@lem4612204 A a)). Qed.
Lemma lem4612207 {A : Type'} (x : A) (a : A) : (term637 A a x) = (term342 A x a).
Proof. exact (eq_refl (term637 A a x)). Qed.
Lemma lem4612208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612209 {A : Type'} (x : A) (a : A) : (term640 A a x) = (term641 A x a).
Proof. exact (MK_COMB (@lem4612208) (@lem4612207 A x a)). Qed.
Lemma lem4612210 {A : Type'} (a : A) : (term639 A a) = (term639 A a).
Proof. exact (eq_refl (term639 A a)). Qed.
Lemma lem4612211 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term639 A a)) = ((term342 A x a) = (term639 A a)).
Proof. exact (MK_COMB (@lem4612209 A x a) (@lem4612210 A a)). Qed.
Lemma lem4612212 {A : Type'} (x : A) (a : A) : ((term637 A a x) = (term638 A a)) = ((term342 A x a) = (term639 A a)).
Proof. exact (TRANS (@lem4612206 A x a) (@lem4612211 A x a)). Qed.
Lemma lem4612213 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term342 A x a) = (term639 A a).
Proof. exact (EQ_MP (@lem4612212 A x a) (@lem4612203 A x a h1)). Qed.
Lemma lem4612214 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : term639 A a.
Proof. exact (EQ_MP (@lem4612213 A x a h2) (@lem4612086 A s x a h1)). Qed.
Lemma lem4612257 {A : Type'} (s : A -> Prop) : (term1066 A s) = (term1066 A s).
Proof. exact (eq_refl (term1066 A s)). Qed.
Lemma lem4612258 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term1067 A s x) = (term1067 A s a).
Proof. exact (MK_COMB (@lem4612257 A s) (@lem4612106 A x a h1)). Qed.
Lemma lem4612259 {A : Type'} (s : A -> Prop) (a : A) : (term1067 A s a) = (term635 A s a).
Proof. exact (eq_refl (term1067 A s a)). Qed.
Lemma lem4612260 {A : Type'} (s : A -> Prop) (x : A) : (term1068 A s x) = (term1068 A s x).
Proof. exact (eq_refl (term1068 A s x)). Qed.
Lemma lem4612261 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term1067 A s x) = (term1067 A s a)) = ((term1067 A s x) = (term635 A s a)).
Proof. exact (MK_COMB (@lem4612260 A s x) (@lem4612259 A s a)). Qed.
Lemma lem4612262 {A : Type'} (s : A -> Prop) (x : A) : (term1067 A s x) = (term635 A s x).
Proof. exact (eq_refl (term1067 A s x)). Qed.
Lemma lem4612263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612264 {A : Type'} (s : A -> Prop) (x : A) : (term1068 A s x) = (term1069 A s x).
Proof. exact (MK_COMB (@lem4612263) (@lem4612262 A s x)). Qed.
Lemma lem4612265 {A : Type'} (s : A -> Prop) (a : A) : (term635 A s a) = (term635 A s a).
Proof. exact (eq_refl (term635 A s a)). Qed.
Lemma lem4612266 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term1067 A s x) = (term635 A s a)) = ((term635 A s x) = (term635 A s a)).
Proof. exact (MK_COMB (@lem4612264 A s x) (@lem4612265 A s a)). Qed.
Lemma lem4612267 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term1067 A s x) = (term1067 A s a)) = ((term635 A s x) = (term635 A s a)).
Proof. exact (TRANS (@lem4612261 A x s a) (@lem4612266 A x s a)). Qed.
Lemma lem4612268 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term635 A s x) = (term635 A s a).
Proof. exact (EQ_MP (@lem4612267 A x s a) (@lem4612258 A s x a h1)). Qed.
Lemma lem4612269 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) (h2 : x = a) : term635 A s a.
Proof. exact (EQ_MP (@lem4612268 A s x a h2) (@lem4612104 A s x a h1)). Qed.
Lemma lem4612297 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : s x.
Proof. exact (proj1 (@lem4611845 A s x a h1)). Qed.
Lemma lem4612298 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : term642 A s x.
Proof. exact (fun h0 : term635 A s x => @lem4612297 A s x a h1). Qed.
Lemma lem4612300 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612301 {A : Type'} (s : A -> Prop) (x : A) : (term642 A s x) = (s x).
Proof. exact (@lem4612300 (s x)). Qed.
Lemma lem4612302 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : s x.
Proof. exact (EQ_MP (@lem4612301 A s x) (@lem4612298 A s x a h1)). Qed.
Lemma lem4612305 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4612307 {A : Type'} (s : A -> Prop) (x : A) : (term635 A s x) = (term651 A s x).
Proof. exact (@lem4612305 (s x)). Qed.
Lemma lem4612310 {A : Type'} (s : A -> Prop) (x : A) (h1 : term635 A s x) : term651 A s x.
Proof. exact (EQ_MP (@lem4612307 A s x) (@lem4612068 A s x h1)). Qed.
Lemma lem4612313 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : False.
Proof. exact (@lem4612310 A s x h1 (@lem4612302 A s x a h2)). Qed.
Lemma lem4612314 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : term652.
Proof. exact (fun h0 : ~ False => @lem4612313 A s x a h1 h2). Qed.
Lemma lem4612316 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612317 : term652 = False.
Proof. exact (@lem4612316 False). Qed.
Lemma lem4612318 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : False.
Proof. exact (EQ_MP (@lem4612317) (@lem4612314 A s x a h1 h2)). Qed.
Lemma lem4612346 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4612347 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4612346 A x). Qed.
Lemma lem4612348 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4612347 A a). Qed.
Lemma lem4612349 {A : Type'} (a : A) : term653 A a.
Proof. exact (fun h0 : term639 A a => @lem4612348 A a). Qed.
Lemma lem4612351 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612352 {A : Type'} (a : A) : (term653 A a) = (a = a).
Proof. exact (@lem4612351 (a = a)). Qed.
Lemma lem4612353 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4612352 A a) (@lem4612349 A a)). Qed.
Lemma lem4612356 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4612358 {A : Type'} (a : A) : (term639 A a) = (term654 A a).
Proof. exact (@lem4612356 (a = a)). Qed.
Lemma lem4612361 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : term654 A a.
Proof. exact (EQ_MP (@lem4612358 A a) (@lem4612214 A s x a h1 h2)). Qed.
Lemma lem4612364 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : False.
Proof. exact (@lem4612361 A s x a h1 h2 (@lem4612353 A a)). Qed.
Lemma lem4612365 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : term652.
Proof. exact (fun h0 : ~ False => @lem4612364 A s x a h1 h2). Qed.
Lemma lem4612367 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612368 : term652 = False.
Proof. exact (@lem4612367 False). Qed.
Lemma lem4612397 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : s a.
Proof. exact (proj2 (@lem4611754 A t s a h1)). Qed.
Lemma lem4612398 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term642 A s a.
Proof. exact (fun h0 : term635 A s a => @lem4612397 A t s a h1). Qed.
Lemma lem4612400 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612401 {A : Type'} (s : A -> Prop) (a : A) : (term642 A s a) = (s a).
Proof. exact (@lem4612400 (s a)). Qed.
Lemma lem4612402 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : s a.
Proof. exact (EQ_MP (@lem4612401 A s a) (@lem4612398 A t s a h1)). Qed.
Lemma lem4612405 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4612407 {A : Type'} (s : A -> Prop) (a : A) : (term635 A s a) = (term651 A s a).
Proof. exact (@lem4612405 (s a)). Qed.
Lemma lem4612410 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) (h2 : x = a) : term651 A s a.
Proof. exact (EQ_MP (@lem4612407 A s a) (@lem4612269 A s x a h1 h2)). Qed.
Lemma lem4612413 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : False.
Proof. exact (@lem4612410 A s x a h2 h3 (@lem4612402 A t s a h1)). Qed.
Lemma lem4612414 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : term652.
Proof. exact (fun h0 : ~ False => @lem4612413 A t s x a h1 h2 h3). Qed.
Lemma lem4612416 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612417 : term652 = False.
Proof. exact (@lem4612416 False). Qed.
Lemma lem4612446 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term343 A s x a) : s x.
Proof. exact (proj1 (@lem4611856 A s x a h1)). Qed.
Lemma lem4612447 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term343 A s x a) : term642 A s x.
Proof. exact (fun h0 : term635 A s x => @lem4612446 A s x a h1). Qed.
Lemma lem4612449 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612450 {A : Type'} (s : A -> Prop) (x : A) : (term642 A s x) = (s x).
Proof. exact (@lem4612449 (s x)). Qed.
Lemma lem4612451 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term343 A s x a) : s x.
Proof. exact (EQ_MP (@lem4612450 A s x) (@lem4612447 A s x a h1)). Qed.
Lemma lem4612454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4612456 {A : Type'} (s : A -> Prop) (x : A) : (term635 A s x) = (term651 A s x).
Proof. exact (@lem4612454 (s x)). Qed.
Lemma lem4612459 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) : term651 A s x.
Proof. exact (EQ_MP (@lem4612456 A s x) (@lem4612122 A s x a h1)). Qed.
Lemma lem4612462 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) (h2 : term343 A s x a) : False.
Proof. exact (@lem4612459 A s x a h1 (@lem4612451 A s x a h2)). Qed.
Lemma lem4612463 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) (h2 : term343 A s x a) : term652.
Proof. exact (fun h0 : ~ False => @lem4612462 A s x a h1 h2). Qed.
Lemma lem4612465 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612466 : term652 = False.
Proof. exact (@lem4612465 False). Qed.
Lemma lem4612467 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1006 A s x a) (h2 : term343 A s x a) : False.
Proof. exact (EQ_MP (@lem4612466) (@lem4612463 A s x a h1 h2)). Qed.
Lemma lem4612495 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : s x.
Proof. exact (proj1 (@lem4611860 A s a t x h1)). Qed.
Lemma lem4612496 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term642 A s x.
Proof. exact (fun h0 : term635 A s x => @lem4612495 A s a t x h1). Qed.
Lemma lem4612498 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612499 {A : Type'} (s : A -> Prop) (x : A) : (term642 A s x) = (s x).
Proof. exact (@lem4612498 (s x)). Qed.
Lemma lem4612500 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : s x.
Proof. exact (EQ_MP (@lem4612499 A s x) (@lem4612496 A s a t x h1)). Qed.
Lemma lem4612502 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term635 A t x.
Proof. exact (proj2 (@lem4611844 A s a t x h1)). Qed.
Lemma lem4612503 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term1070 A t x.
Proof. exact (fun h0 : t x => @lem4612502 A s a t x h1). Qed.
Lemma lem4612505 (p : Prop) : (term909 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4612506 {A : Type'} (t : A -> Prop) (x : A) : (term1070 A t x) = (term635 A t x).
Proof. exact (@lem4612505 (t x)). Qed.
Lemma lem4612507 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term635 A t x.
Proof. exact (EQ_MP (@lem4612506 A t x) (@lem4612503 A s a t x h1)). Qed.
Lemma lem4612513 (q : Prop) (p : Prop) (r : Prop) : (term662 p q r) = (term662 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4612514 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1065 A s a t _55398) = (term1071 A a s t _55398).
Proof. exact (@lem4612513 (_55398 = a) (term635 A s _55398) (t _55398)). Qed.
Lemma lem4612530 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4612531 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55398 : A) : (term437 A s t _55398) = (term644 A t s _55398).
Proof. exact (@lem4612530 (t _55398) (term635 A s _55398)). Qed.
Lemma lem4612537 {A : Type'} (_55398 : A) (a : A) : (term359 A _55398 a) = (term359 A _55398 a).
Proof. exact (eq_refl (term359 A _55398 a)). Qed.
Lemma lem4612538 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55398 : A) : (term1071 A a s t _55398) = (term1072 A a t s _55398).
Proof. exact (MK_COMB (@lem4612537 A _55398 a) (@lem4612531 A t s _55398)). Qed.
Lemma lem4612542 (q : Prop) (p : Prop) (r : Prop) : (term662 p q r) = (term662 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4612543 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1072 A a t s _55398) = (term1073 A t a s _55398).
Proof. exact (@lem4612542 (t _55398) (_55398 = a) (term635 A s _55398)). Qed.
Lemma lem4612561 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1071 A a s t _55398) = (term1073 A t a s _55398).
Proof. exact (TRANS (@lem4612538 A a t s _55398) (@lem4612543 A t a s _55398)). Qed.
Lemma lem4612562 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1065 A s a t _55398) = (term1073 A t a s _55398).
Proof. exact (TRANS (@lem4612514 A a s t _55398) (@lem4612561 A t a s _55398)). Qed.
Lemma lem4612563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612564 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1074 A s a t _55398) = (term1075 A t a s _55398).
Proof. exact (MK_COMB (@lem4612563) (@lem4612562 A t a s _55398)). Qed.
Lemma lem4612580 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4612581 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_55398 : A) : (term437 A s t _55398) = (term644 A t s _55398).
Proof. exact (@lem4612580 (t _55398) (term635 A s _55398)). Qed.
Lemma lem4612587 {A : Type'} (_55398 : A) (a : A) : (term359 A _55398 a) = (term359 A _55398 a).
Proof. exact (eq_refl (term359 A _55398 a)). Qed.
Lemma lem4612588 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) (_55398 : A) : (term1071 A a s t _55398) = (term1072 A a t s _55398).
Proof. exact (MK_COMB (@lem4612587 A _55398 a) (@lem4612581 A t s _55398)). Qed.
Lemma lem4612592 (q : Prop) (p : Prop) (r : Prop) : (term662 p q r) = (term662 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4612593 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1072 A a t s _55398) = (term1073 A t a s _55398).
Proof. exact (@lem4612592 (t _55398) (_55398 = a) (term635 A s _55398)). Qed.
Lemma lem4612611 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : (term1071 A a s t _55398) = (term1073 A t a s _55398).
Proof. exact (TRANS (@lem4612588 A a t s _55398) (@lem4612593 A t a s _55398)). Qed.
Lemma lem4612612 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : ((term1065 A s a t _55398) = (term1071 A a s t _55398)) = ((term1073 A t a s _55398) = (term1073 A t a s _55398)).
Proof. exact (MK_COMB (@lem4612564 A t a s _55398) (@lem4612611 A t a s _55398)). Qed.
Lemma lem4612614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4612615 (x : Prop) : (x = x) = True.
Proof. exact (@lem4612614 Prop x). Qed.
Lemma lem4612616 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (_55398 : A) : ((term1073 A t a s _55398) = (term1073 A t a s _55398)) = True.
Proof. exact (@lem4612615 (term1073 A t a s _55398)). Qed.
Lemma lem4612617 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) (_55398 : A) : ((term1065 A s a t _55398) = (term1071 A a s t _55398)) = True.
Proof. exact (TRANS (@lem4612612 A t a s _55398) (@lem4612616 A t a s _55398)). Qed.
Lemma lem4612618 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) (_55398 : A) : True = ((term1065 A s a t _55398) = (term1071 A a s t _55398)).
Proof. exact (SYM (@lem4612617 A a s t _55398)). Qed.
Lemma lem4612619 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1065 A s a t _55398) = (term1071 A a s t _55398).
Proof. exact (EQ_MP (@lem4612618 A a s t _55398) (@lem0)). Qed.
Lemma lem4612620 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1071 A a s t _55398.
Proof. exact (EQ_MP (@lem4612619 A a s t _55398) (@lem4612138 A _55398 t s a h1)). Qed.
Lemma lem4612622 (b : Prop) (a : Prop) : (a \/ b) = (term647 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4612623 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) (a : A) : (term1071 A a s t _55398) = (term1076 A s t _55398 a).
Proof. exact (@lem4612622 (term437 A s t _55398) (_55398 = a)). Qed.
Lemma lem4612625 (a : Prop) (b : Prop) : (term911 a b) = (term912 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4612626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1077 A s t _55398) = (term1078 A s t _55398).
Proof. exact (@lem4612625 (term635 A s _55398) (t _55398)). Qed.
Lemma lem4612628 (a : Prop) : (term382 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4612629 {A : Type'} (s : A -> Prop) (_55398 : A) : (term649 A s _55398) = (s _55398).
Proof. exact (@lem4612628 (s _55398)). Qed.
Lemma lem4612630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4612631 {A : Type'} (s : A -> Prop) (_55398 : A) : (term1079 A s _55398) = (term341 A s _55398).
Proof. exact (MK_COMB (@lem4612630) (@lem4612629 A s _55398)). Qed.
Lemma lem4612632 {A : Type'} (t : A -> Prop) (_55398 : A) : (term635 A t _55398) = (term635 A t _55398).
Proof. exact (eq_refl (term635 A t _55398)). Qed.
Lemma lem4612633 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1078 A s t _55398) = (term724 A s t _55398).
Proof. exact (MK_COMB (@lem4612631 A s _55398) (@lem4612632 A t _55398)). Qed.
Lemma lem4612634 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1077 A s t _55398) = (term724 A s t _55398).
Proof. exact (TRANS (@lem4612626 A s t _55398) (@lem4612633 A s t _55398)). Qed.
Lemma lem4612635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4612636 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) : (term1080 A s t _55398) = (term1081 A s t _55398).
Proof. exact (MK_COMB (@lem4612635) (@lem4612634 A s t _55398)). Qed.
Lemma lem4612637 {A : Type'} (_55398 : A) (a : A) : (_55398 = a) = (_55398 = a).
Proof. exact (eq_refl (_55398 = a)). Qed.
Lemma lem4612638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) (a : A) : (term1076 A s t _55398 a) = (term1082 A s t _55398 a).
Proof. exact (MK_COMB (@lem4612636 A s t _55398) (@lem4612637 A _55398 a)). Qed.
Lemma lem4612639 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_55398 : A) (a : A) : (term1071 A a s t _55398) = (term1082 A s t _55398 a).
Proof. exact (TRANS (@lem4612623 A s t _55398 a) (@lem4612638 A s t _55398 a)). Qed.
Lemma lem4612641 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term724 A s t x.
Proof. exact (conj (@lem4612500 A s a t x h1) (@lem4612507 A s a t x h1)). Qed.
Lemma lem4612643 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1082 A s t _55398 a.
Proof. exact (EQ_MP (@lem4612639 A s t _55398 a) (@lem4612620 A _55398 t s a h1)). Qed.
Lemma lem4612644 {A : Type'} (_55398 : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1082 A s t _55398 a.
Proof. exact (@lem4612643 A _55398 t s a h1). Qed.
Lemma lem4612645 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term1082 A s t x a.
Proof. exact (@lem4612644 A x t s a h1). Qed.
Lemma lem4612648 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : x = a.
Proof. exact (@lem4612645 A x t s a h1 (@lem4612641 A s a t x h2)). Qed.
Lemma lem4612649 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : term1083 A x a.
Proof. exact (fun h0 : term342 A x a => @lem4612648 A s a t x h1 h2). Qed.
Lemma lem4612651 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612652 {A : Type'} (x : A) (a : A) : (term1083 A x a) = (x = a).
Proof. exact (@lem4612651 (x = a)). Qed.
Lemma lem4612653 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : x = a.
Proof. exact (EQ_MP (@lem4612652 A x a) (@lem4612649 A s a t x h1 h2)). Qed.
Lemma lem4612656 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4612658 {A : Type'} (x : A) (a : A) : (term342 A x a) = (term1084 A x a).
Proof. exact (@lem4612656 (x = a)). Qed.
Lemma lem4612661 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A s a t x) : term1084 A x a.
Proof. exact (EQ_MP (@lem4612658 A x a) (@lem4612146 A s a t x h1)). Qed.
Lemma lem4612664 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : False.
Proof. exact (@lem4612661 A s a t x h2 (@lem4612653 A s a t x h1 h2)). Qed.
Lemma lem4612665 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : term652.
Proof. exact (fun h0 : ~ False => @lem4612664 A s a t x h1 h2). Qed.
Lemma lem4612667 (p : Prop) : (term643 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4612668 : term652 = False.
Proof. exact (@lem4612667 False). Qed.
Lemma lem4612669 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term441 A s a t x) : False.
Proof. exact (EQ_MP (@lem4612668) (@lem4612665 A s a t x h1 h2)). Qed.
Lemma lem4612670 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4612417) (@lem4612414 A t s x a h1 h2 h3)). Qed.
Lemma lem4612671 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4612368) (@lem4612365 A s x a h1 h2)). Qed.
Lemma lem4612672 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4612670 A t s x a h1 h2 h3) (fun h4 : False => @lem4612106 A x a h3)). Qed.
Lemma lem4612673 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4612672 A t s x a h1 h2 h3) (@lem4612106 A x a h3)). Qed.
Lemma lem4612674 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4612671 A s x a h1 h2) (fun h3 : False => @lem4612088 A x a h2)). Qed.
Lemma lem4612675 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4612674 A s x a h1 h2) (@lem4612088 A x a h2)). Qed.
Lemma lem4612676 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : (term635 A s x) = False.
Proof. exact (prop_ext (fun h3 : term635 A s x => @lem4612318 A s x a h1 h2) (fun h3 : False => @lem4612068 A s x h1)). Qed.
Lemma lem4612677 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : False.
Proof. exact (EQ_MP (@lem4612676 A s x a h1 h2) (@lem4612068 A s x h1)). Qed.
Lemma lem4612678 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4612673 A t s x a h1 h2 h3) (fun h4 : False => @lem4611963 A x a h3)). Qed.
Lemma lem4612679 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4612678 A t s x a h1 h2 h3) (@lem4611963 A x a h3)). Qed.
Lemma lem4612680 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4612675 A s x a h1 h2) (fun h3 : False => @lem4611932 A x a h2)). Qed.
Lemma lem4612681 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4612680 A s x a h1 h2) (@lem4611932 A x a h2)). Qed.
Lemma lem4612682 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : (term635 A s x) = False.
Proof. exact (prop_ext (fun h3 : term635 A s x => @lem4612677 A s x a h1 h2) (fun h3 : False => @lem4611897 A s x h1)). Qed.
Lemma lem4612683 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : False.
Proof. exact (EQ_MP (@lem4612682 A s x a h1 h2) (@lem4611897 A s x h1)). Qed.
Lemma lem4612684 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem4612679 A t s x a h1 h2 h3) (fun h4 : False => @lem4611963 A x a h3)). Qed.
Lemma lem4612685 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem4612684 A t s x a h1 h2 h3) (@lem4611963 A x a h3)). Qed.
Lemma lem4612686 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4612681 A s x a h1 h2) (fun h3 : False => @lem4611932 A x a h2)). Qed.
Lemma lem4612687 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4612686 A s x a h1 h2) (@lem4611932 A x a h2)). Qed.
Lemma lem4612688 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : (term635 A s x) = False.
Proof. exact (prop_ext (fun h3 : term635 A s x => @lem4612683 A s x a h1 h2) (fun h3 : False => @lem4611897 A s x h1)). Qed.
Lemma lem4612689 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term635 A s x) (h2 : term1008 A s x a) : False.
Proof. exact (EQ_MP (@lem4612688 A s x a h1 h2) (@lem4611897 A s x h1)). Qed.
Lemma lem4612690 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1006 A s x a) : False.
Proof. exact (or_elim (@lem4611853 A s x a h2) (fun h0 : x = a => @lem4612685 A t s x a h1 h2 h0) (fun h0 : term343 A s x a => @lem4612467 A s x a h2 h0)). Qed.
Lemma lem4612691 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term1008 A s x a) : False.
Proof. exact (or_elim (@lem4611849 A s x a h1) (fun h0 : term635 A s x => @lem4612689 A s x a h0 h1) (fun h0 : x = a => @lem4612687 A s x a h1 h0)). Qed.
Lemma lem4612692 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (a : A) (h1 : term969 A t s a) (h2 : term1012 A s x a) : False.
Proof. exact (or_elim (@lem4611843 A s x a h2) (fun h0 : term1008 A s x a => @lem4612691 A s x a h0) (fun h0 : term1006 A s x a => @lem4612690 A t s x a h1 h0)). Qed.
Lemma lem4612693 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term1060 A s a t x) : False.
Proof. exact (or_elim (@lem4611840 A s a t x h2) (fun h0 : term1012 A s x a => @lem4612692 A t s x a h1 h0) (fun h0 : term441 A s a t x => @lem4612669 A s a t x h1 h0)). Qed.
Lemma lem4612694 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term1060 A s a t x) : (term1060 A s a t x) = False.
Proof. exact (prop_ext (fun h3 : term1060 A s a t x => @lem4612693 A s a t x h1 h2) (fun h3 : False => @lem4611840 A s a t x h2)). Qed.
Lemma lem4612695 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term969 A t s a) (h2 : term1060 A s a t x) : False.
Proof. exact (EQ_MP (@lem4612694 A s a t x h1 h2) (@lem4611840 A s a t x h2)). Qed.
Lemma lem4612696 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term999 A s a t) (h2 : term969 A t s a) : False.
Proof. exact (ex_elim (@lem4611724 A s a t h1) (fun x : A => fun h0 : term1062 A s a t x => @lem4612695 A s a t x h2 h0)). Qed.
Lemma lem4612697 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term999 A s a t) (h2 : term969 A t s a) : (term999 A s a t) = False.
Proof. exact (prop_ext (fun h3 : term999 A s a t => @lem4612696 A t s a h1 h2) (fun h3 : False => @lem4611375 A s a t h1)). Qed.
Lemma lem4612698 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term999 A s a t) (h2 : term969 A t s a) : False.
Proof. exact (EQ_MP (@lem4612697 A t s a h1 h2) (@lem4611375 A s a t h1)). Qed.
Lemma lem4612699 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term998 A s a t.
Proof. exact (fun h0 : term999 A s a t => @lem4612698 A t s a h0 h1). Qed.
Lemma lem4612700 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) (h1 : term969 A t s a) : term978 A s a t.
Proof. exact (EQ_MP (@lem4611374 A s a t) (@lem4612699 A t s a h1)). Qed.
Lemma lem4612701 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term979 A s a t.
Proof. exact (fun h0 : term969 A t s a => @lem4612700 A t s a h0). Qed.
Lemma lem4612706 {A : Type'} (a : A) (t : A -> Prop) : term989 A a t.
Proof. exact (fun s : A -> Prop => @lem4612701 A s a t). Qed.
Lemma lem4612711 {A : Type'} (t : A -> Prop) : term993 A t.
Proof. exact (fun a : A => @lem4612706 A a t). Qed.
Lemma lem4612716 {A : Type'} : term997 A.
Proof. exact (fun t : A -> Prop => @lem4612711 A t). Qed.
Lemma lem4612717 {A : Type'} : term996 A.
Proof. exact (EQ_MP (@lem4611369 A) (@lem4612716 A)). Qed.
Lemma lem4612718 {A : Type'} (t : A -> Prop) : term1085 A t.
Proof. exact (@lem4612717 A t). Qed.
Lemma lem4612719 {A : Type'} (t : A -> Prop) : (term1085 A t) = (term992 A t).
Proof. exact (eq_refl (term1085 A t)). Qed.
Lemma lem4612720 {A : Type'} (t : A -> Prop) : term992 A t.
Proof. exact (EQ_MP (@lem4612719 A t) (@lem4612718 A t)). Qed.
Lemma lem4612721 {A : Type'} (t : A -> Prop) (a : A) : term1086 A t a.
Proof. exact (@lem4612720 A t a). Qed.
Lemma lem4612722 {A : Type'} (a : A) (t : A -> Prop) : (term1086 A t a) = (term988 A a t).
Proof. exact (eq_refl (term1086 A t a)). Qed.
Lemma lem4612723 {A : Type'} (a : A) (t : A -> Prop) : term988 A a t.
Proof. exact (EQ_MP (@lem4612722 A a t) (@lem4612721 A t a)). Qed.
Lemma lem4612724 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) : term1087 A a t s.
Proof. exact (@lem4612723 A a t s). Qed.
Lemma lem4612725 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term1087 A a t s) = (term980 A s a t).
Proof. exact (eq_refl (term1087 A a t s)). Qed.
Lemma lem4612726 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term980 A s a t.
Proof. exact (EQ_MP (@lem4612725 A s a t) (@lem4612724 A a t s)). Qed.
Lemma lem4612728 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term980 A s a t.
Proof. exact (@lem4611172 A s a t (@lem4612726 A s a t)). Qed.
Lemma lem4612729 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term981 A s a t) : False.
Proof. exact (@lem4612728 A s a t (@lem4611156 A s a t h1)). Qed.
Lemma lem4612730 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term981 A s a t) : (term981 A s a t) = False.
Proof. exact (prop_ext (fun h2 : term981 A s a t => @lem4612729 A s a t h1) (fun h2 : False => @lem4611156 A s a t h1)). Qed.
Lemma lem4612731 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term981 A s a t) : False.
Proof. exact (EQ_MP (@lem4612730 A s a t h1) (@lem4611156 A s a t h1)). Qed.
Lemma lem4612732 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term980 A s a t.
Proof. exact (fun h0 : term981 A s a t => @lem4612731 A s a t h0). Qed.
Lemma lem4612733 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term979 A s a t.
Proof. exact (EQ_MP (@lem4611155 A s a t) (@lem4612732 A s a t)). Qed.
Lemma lem4612734 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term967 A s a t.
Proof. exact (EQ_MP (@lem4611151 A s a t) (@lem4612733 A s a t)). Qed.
Lemma lem4612735 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term966 A s a t.
Proof. exact (EQ_MP (@lem4610989 A s a t) (@lem4612734 A s a t)). Qed.
Lemma lem4612736 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : term964 A s a t.
Proof. exact (@lem4612735 A s a t (@lem4610932 A s a t h1 h2)). Qed.
Lemma lem4612737 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : term290 A s a t.
Proof. exact (ex_intro (term289 A s a t) (@DELETE A s a) (@lem4612736 A s a t h1 h2)). Qed.
Lemma lem4612738 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : term291 A s a t.
Proof. exact (or_intro2 (@SUBSET A s t) (@lem4612737 A s a t h1 h2)). Qed.
Lemma lem4612739 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : (term62 A s a t) = (term291 A s a t).
Proof. exact (prop_ext (fun h3 : term62 A s a t => @lem4612738 A s a t h1 h2) (fun h3 : term291 A s a t => @lem4610921 A s a t h2)). Qed.
Lemma lem4612740 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : @IN A a s) (h2 : term62 A s a t) : term291 A s a t.
Proof. exact (EQ_MP (@lem4612739 A s a t h1 h2) (@lem4610921 A s a t h2)). Qed.
Lemma lem4612741 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term292 A s a t.
Proof. exact (fun h0 : term62 A s a t => @lem4612740 A s a t h1 h0). Qed.
Lemma lem4612742 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term292 A s a t.
Proof. exact (or_elim (@lem4606460 A a s) (fun h0 : @IN A a s => @lem4612741 A t a s h0) (fun h0 : term2 A a s => @lem4610920 A t a s h0)). Qed.
Lemma lem4612747 {A : Type'} (a : A) (t : A -> Prop) : term294 A a t.
Proof. exact (fun s : A -> Prop => @lem4612742 A s a t). Qed.
Lemma lem4612748 {A : Type'} (a : A) (t : A -> Prop) : term317 A a t.
Proof. exact (conj (@lem4612747 A a t) (@lem4609184 A a t)). Qed.
Lemma lem4612749 {A : Type'} (a : A) (t : A -> Prop) : term262 A a t.
Proof. exact (EQ_MP (@lem4607312 A a t) (@lem4612748 A a t)). Qed.
Lemma lem4612750 {A : Type'} (a : A) (t : A -> Prop) : term126 A a t.
Proof. exact (EQ_MP (@lem4607104 A a t) (@lem4612749 A a t)). Qed.
Lemma lem4612751 {A : Type'} (a : A) (t : A -> Prop) : term114 A a t.
Proof. exact (EQ_MP (@lem4606823 A a t) (@lem4612750 A a t)). Qed.
Lemma lem4612752 {A : Type'} (a : A) (t : A -> Prop) : term113 A a t.
Proof. exact (EQ_MP (@lem4606800 A a t) (@lem4612751 A a t)). Qed.
Lemma lem4612753 {A : Type'} (a : A) (t : A -> Prop) : (term90 A a t) = (term93 A a t).
Proof. exact (@lem4606759 A a t (@lem4612752 A a t)). Qed.
Lemma lem4612758 {A : Type'} (a : A) : term97 A a.
Proof. exact (fun t : A -> Prop => @lem4612753 A a t). Qed.
Lemma lem4612763 {A : Type'} : term101 A.
Proof. exact (fun a : A => @lem4612758 A a). Qed.
Lemma lem4612764 {_108216 A : Type'} : term102 _108216 A.
Proof. exact (EQ_MP (@lem4606755 _108216 A) (@lem4612763 A)). Qed.
