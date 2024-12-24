Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8050938_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8050664 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8050665 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8050666 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8050665 _141927 _141928 _141929 s) (@lem8050664 _141927 _141928 _141929 s)). Qed.
Lemma lem8050667 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8050666 _141927 _141928 _141929 s t). Qed.
Lemma lem8050668 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050669 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8050668 _141927 _141928 _141929 s t) (@lem8050667 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050670 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8050669 _141927 _141928 _141929 s t x). Qed.
Lemma lem8050671 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050672 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8050671 _141927 _141928 _141929 x s t) (@lem8050670 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050673 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8050672 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8050674 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050700 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem8050701 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem8050700 _83095 p). Qed.
Lemma lem8050702 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem8050703 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem8050702 _83095 p) (@lem8050701 _83095 p)). Qed.
Lemma lem8050704 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem8050703 _83095 p x). Qed.
Lemma lem8050705 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem8050714 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8050715 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8050716 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8050715 A s) (@lem8050714 A s)). Qed.
Lemma lem8050717 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8050716 A s t). Qed.
Lemma lem8050718 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8050735 {_89711 _89725 : Type'} : term18 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem8050736 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term19 _89711 _89725 P.
Proof. exact (@lem8050735 _89711 _89725 P). Qed.
Lemma lem8050737 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term19 _89711 _89725 P) = (term20 _89711 _89725 P).
Proof. exact (eq_refl (term19 _89711 _89725 P)). Qed.
Lemma lem8050738 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term20 _89711 _89725 P.
Proof. exact (EQ_MP (@lem8050737 _89711 _89725 P) (@lem8050736 _89711 _89725 P)). Qed.
Lemma lem8050739 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term21 _89711 _89725 P f.
Proof. exact (@lem8050738 _89711 _89725 P f). Qed.
Lemma lem8050740 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P f) = ((term22 _89711 _89725 P f) = (term23 _89711 _89725 P f)).
Proof. exact (eq_refl (term21 _89711 _89725 P f)). Qed.
Lemma lem8050758 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8050718 A s t) (@lem8050717 A s t)). Qed.
Lemma lem8050759 {_143061 _143062 _143063 : Type'} (s : type16 _143061 _143062 _143063) (t : type16 _143061 _143062 _143063) : (s = t) = (term24 _143061 _143062 _143063 s t).
Proof. exact (@lem8050758 (type2 _143061 _143062 _143063) s t). Qed.
Lemma lem8050760 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term25 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t)) = (term27 _143061 _143062 _143063 f t).
Proof. exact (@lem8050759 _143061 _143062 _143063 (term25 _143061 _143062 _143063 f t) (term26 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050766 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term28 _140454 _140455 _140456 P) = (term29 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8050767 {_143061 _143062 _143063 : Type'} (P : type16 _143061 _143062 _143063) : (term28 _143061 _143062 _143063 P) = (term29 _143061 _143062 _143063 P).
Proof. exact (@lem8050766 _143061 _143062 _143063 P). Qed.
Lemma lem8050768 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term30 _143061 _143062 _143063 f t) = (term31 _143061 _143062 _143063 f t).
Proof. exact (@lem8050767 _143061 _143062 _143063 (term32 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050769 {_143061 _143062 _143063 : Type'} (x : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term33 _143061 _143062 _143063 f t x) = ((term34 _143061 _143062 _143063 x f t) = (term35 _143061 _143062 _143063 x f t)).
Proof. exact (eq_refl (term33 _143061 _143062 _143063 f t x)). Qed.
Lemma lem8050770 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term36 _143061 _143062 _143063 f t) = (term32 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : type2 _143061 _143062 _143063 => @lem8050769 _143061 _143062 _143063 x f t)). Qed.
Lemma lem8050771 {_143061 _143062 _143063 : Type'} : (@all (cart _143061 (finite_sum _143062 _143063))) = (@all (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@all (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050772 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term30 _143061 _143062 _143063 f t) = (term27 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050771 _143061 _143062 _143063) (@lem8050770 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050774 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term37 _143061 _143062 _143063 f t) = (term38 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050773) (@lem8050772 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050775 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term39 _143061 _143062 _143063 f t x y) = ((term40 _143061 _143062 _143063 x y f t) = (term41 _143061 _143062 _143063 x y f t)).
Proof. exact (eq_refl (term39 _143061 _143062 _143063 f t x y)). Qed.
Lemma lem8050776 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term42 _143061 _143062 _143063 f t x) = (term43 _143061 _143062 _143063 x f t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8050775 _143061 _143062 _143063 x y f t)). Qed.
Lemma lem8050777 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8050778 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term44 _143061 _143062 _143063 f t x) = (term45 _143061 _143062 _143063 x f t).
Proof. exact (MK_COMB (@lem8050777 _143061 _143063) (@lem8050776 _143061 _143062 _143063 x f t)). Qed.
Lemma lem8050779 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term46 _143061 _143062 _143063 f t) = (term47 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8050778 _143061 _143062 _143063 x f t)). Qed.
Lemma lem8050780 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8050781 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term31 _143061 _143062 _143063 f t) = (term48 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050780 _143061 _143062) (@lem8050779 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050782 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term30 _143061 _143062 _143063 f t) = (term31 _143061 _143062 _143063 f t)) = ((term27 _143061 _143062 _143063 f t) = (term48 _143061 _143062 _143063 f t)).
Proof. exact (MK_COMB (@lem8050774 _143061 _143062 _143063 f t) (@lem8050781 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050783 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term27 _143061 _143062 _143063 f t) = (term48 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8050782 _143061 _143062 _143063 f t) (@lem8050768 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050790 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term25 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t)) = (term48 _143061 _143062 _143063 f t).
Proof. exact (TRANS (@lem8050760 _143061 _143062 _143063 f t) (@lem8050783 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050802 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050674 _141927 _141928 _141929 x s y t) (@lem8050673 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050803 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (s : type24 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 x y s t) = (term8 _143061 _143062 _143063 x s y t).
Proof. exact (@lem8050802 _143061 _143062 _143063 x s y t). Qed.
Lemma lem8050804 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term40 _143061 _143062 _143063 x y f t) = (term49 _143061 _143062 _143063 x f y t).
Proof. exact (@lem8050803 _143061 _143062 _143063 x (@INTERS (cart _143061 _143062) f) y t). Qed.
Lemma lem8050807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050808 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (f : type56 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term50 _143061 _143062 _143063 x y f t) = (term51 _143061 _143062 _143063 x f y t).
Proof. exact (MK_COMB (@lem8050807) (@lem8050804 _143061 _143062 _143063 x f y t)). Qed.
Lemma lem8050810 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P f) = (term23 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem8050740 _89711 _89725 P f) (@lem8050739 _89711 _89725 P f)). Qed.
Lemma lem8050811 {_143061 _143062 _143063 : Type'} (P : type56 _143061 _143062) (f : type52 _143061 _143062 _143063) : (term52 _143061 _143062 _143063 P f) = (term53 _143061 _143062 _143063 P f).
Proof. exact (@lem8050810 (type2 _143061 _143062 _143063) (type24 _143061 _143062) P f). Qed.
Lemma lem8050812 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term54 _143061 _143062 _143063 f t) = (term55 _143061 _143062 _143063 f t).
Proof. exact (@lem8050811 _143061 _143062 _143063 (term56 _143061 _143062 f) (term57 _143061 _143062 _143063 t)). Qed.
Lemma lem8050813 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) : (term58 _143061 _143062 f s) = (@IN ((cart _143061 _143062) -> Prop) s f).
Proof. exact (eq_refl (term58 _143061 _143062 f s)). Qed.
Lemma lem8050814 {_143061 _143062 _143063 : Type'} (GEN_PVAR_369 : type16 _143061 _143062 _143063) : (@SETSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop) GEN_PVAR_369) = (@SETSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop) GEN_PVAR_369).
Proof. exact (eq_refl (@SETSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop) GEN_PVAR_369)). Qed.
Lemma lem8050815 {_143061 _143062 _143063 : Type'} (GEN_PVAR_369 : type16 _143061 _143062 _143063) (s : type24 _143061 _143062) (f : type56 _143061 _143062) : (term59 _143061 _143062 _143063 GEN_PVAR_369 f s) = (term60 _143061 _143062 _143063 GEN_PVAR_369 s f).
Proof. exact (MK_COMB (@lem8050814 _143061 _143062 _143063 GEN_PVAR_369) (@lem8050813 _143061 _143062 s f)). Qed.
Lemma lem8050816 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (t : type24 _143061 _143063) : (term61 _143061 _143062 _143063 t s) = (@PCROSS _143061 _143062 _143063 s t).
Proof. exact (eq_refl (term61 _143061 _143062 _143063 t s)). Qed.
Lemma lem8050817 {_143061 _143062 _143063 : Type'} (GEN_PVAR_369 : type16 _143061 _143062 _143063) (f : type56 _143061 _143062) (s : type24 _143061 _143062) (t : type24 _143061 _143063) : (term62 _143061 _143062 _143063 GEN_PVAR_369 f t s) = (term63 _143061 _143062 _143063 GEN_PVAR_369 f s t).
Proof. exact (MK_COMB (@lem8050815 _143061 _143062 _143063 GEN_PVAR_369 s f) (@lem8050816 _143061 _143062 _143063 s t)). Qed.
Lemma lem8050818 {_143061 _143062 _143063 : Type'} (GEN_PVAR_369 : type16 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term64 _143061 _143062 _143063 GEN_PVAR_369 f t) = (term65 _143061 _143062 _143063 GEN_PVAR_369 f t).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8050817 _143061 _143062 _143063 GEN_PVAR_369 f s t)). Qed.
Lemma lem8050819 {_143061 _143062 : Type'} : (@ex ((cart _143061 _143062) -> Prop)) = (@ex ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8050820 {_143061 _143062 _143063 : Type'} (GEN_PVAR_369 : type16 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term66 _143061 _143062 _143063 GEN_PVAR_369 f t) = (term67 _143061 _143062 _143063 GEN_PVAR_369 f t).
Proof. exact (MK_COMB (@lem8050819 _143061 _143062) (@lem8050818 _143061 _143062 _143063 GEN_PVAR_369 f t)). Qed.
Lemma lem8050821 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term68 _143061 _143062 _143063 f t) = (term69 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun GEN_PVAR_369 : type16 _143061 _143062 _143063 => @lem8050820 _143061 _143062 _143063 GEN_PVAR_369 f t)). Qed.
Lemma lem8050822 {_143061 _143062 _143063 : Type'} : (@GSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop)) = (@GSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((cart _143061 (finite_sum _143062 _143063)) -> Prop))). Qed.
Lemma lem8050823 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term70 _143061 _143062 _143063 f t) = (term71 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050822 _143061 _143062 _143063) (@lem8050821 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050824 {_143061 _143062 _143063 : Type'} : (@INTERS (cart _143061 (finite_sum _143062 _143063))) = (@INTERS (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@INTERS (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050825 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term54 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050824 _143061 _143062 _143063) (@lem8050823 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050826 {_143061 _143062 _143063 : Type'} : (@eq ((cart _143061 (finite_sum _143062 _143063)) -> Prop)) = (@eq ((cart _143061 (finite_sum _143062 _143063)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _143061 (finite_sum _143062 _143063)) -> Prop))). Qed.
Lemma lem8050827 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term72 _143061 _143062 _143063 f t) = (term73 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050826 _143061 _143062 _143063) (@lem8050825 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050828 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) : (term58 _143061 _143062 f s) = (@IN ((cart _143061 _143062) -> Prop) s f).
Proof. exact (eq_refl (term58 _143061 _143062 f s)). Qed.
Lemma lem8050829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8050830 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) : (term74 _143061 _143062 f s) = (term75 _143061 _143062 s f).
Proof. exact (MK_COMB (@lem8050829) (@lem8050828 _143061 _143062 s f)). Qed.
Lemma lem8050831 {_143061 _143062 _143063 : Type'} (s : type24 _143061 _143062) (t : type24 _143061 _143063) : (term61 _143061 _143062 _143063 t s) = (@PCROSS _143061 _143062 _143063 s t).
Proof. exact (eq_refl (term61 _143061 _143062 _143063 t s)). Qed.
Lemma lem8050832 {_143061 _143062 _143063 : Type'} (a : type2 _143061 _143062 _143063) : (@IN (cart _143061 (finite_sum _143062 _143063)) a) = (@IN (cart _143061 (finite_sum _143062 _143063)) a).
Proof. exact (eq_refl (@IN (cart _143061 (finite_sum _143062 _143063)) a)). Qed.
Lemma lem8050833 {_143061 _143062 _143063 : Type'} (a : type2 _143061 _143062 _143063) (s : type24 _143061 _143062) (t : type24 _143061 _143063) : (term76 _143061 _143062 _143063 a t s) = (term77 _143061 _143062 _143063 a s t).
Proof. exact (MK_COMB (@lem8050832 _143061 _143062 _143063 a) (@lem8050831 _143061 _143062 _143063 s t)). Qed.
Lemma lem8050834 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (s : type24 _143061 _143062) (t : type24 _143061 _143063) : (term78 _143061 _143062 _143063 f a t s) = (term79 _143061 _143062 _143063 f a s t).
Proof. exact (MK_COMB (@lem8050830 _143061 _143062 s f) (@lem8050833 _143061 _143062 _143063 a s t)). Qed.
Lemma lem8050835 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term80 _143061 _143062 _143063 f a t) = (term81 _143061 _143062 _143063 f a t).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8050834 _143061 _143062 _143063 f a s t)). Qed.
Lemma lem8050836 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8050837 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term82 _143061 _143062 _143063 f a t) = (term83 _143061 _143062 _143063 f a t).
Proof. exact (MK_COMB (@lem8050836 _143061 _143062) (@lem8050835 _143061 _143062 _143063 f a t)). Qed.
Lemma lem8050838 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) : (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56) = (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56)). Qed.
Lemma lem8050839 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term84 _143061 _143062 _143063 GEN_PVAR_56 f a t) = (term85 _143061 _143062 _143063 GEN_PVAR_56 f a t).
Proof. exact (MK_COMB (@lem8050838 _143061 _143062 _143063 GEN_PVAR_56) (@lem8050837 _143061 _143062 _143063 f a t)). Qed.
Lemma lem8050840 {_143061 _143062 _143063 : Type'} (a : type2 _143061 _143062 _143063) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8050841 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (a : type2 _143061 _143062 _143063) : (term86 _143061 _143062 _143063 GEN_PVAR_56 f t a) = (term87 _143061 _143062 _143063 GEN_PVAR_56 f t a).
Proof. exact (MK_COMB (@lem8050839 _143061 _143062 _143063 GEN_PVAR_56 f a t) (@lem8050840 _143061 _143062 _143063 a)). Qed.
Lemma lem8050842 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term88 _143061 _143062 _143063 GEN_PVAR_56 f t) = (term89 _143061 _143062 _143063 GEN_PVAR_56 f t).
Proof. exact (fun_ext (fun a : type2 _143061 _143062 _143063 => @lem8050841 _143061 _143062 _143063 GEN_PVAR_56 f t a)). Qed.
Lemma lem8050843 {_143061 _143062 _143063 : Type'} : (@ex (cart _143061 (finite_sum _143062 _143063))) = (@ex (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@ex (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050844 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term90 _143061 _143062 _143063 GEN_PVAR_56 f t) = (term91 _143061 _143062 _143063 GEN_PVAR_56 f t).
Proof. exact (MK_COMB (@lem8050843 _143061 _143062 _143063) (@lem8050842 _143061 _143062 _143063 GEN_PVAR_56 f t)). Qed.
Lemma lem8050845 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term92 _143061 _143062 _143063 f t) = (term93 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _143061 _143062 _143063 => @lem8050844 _143061 _143062 _143063 GEN_PVAR_56 f t)). Qed.
Lemma lem8050846 {_143061 _143062 _143063 : Type'} : (@GSPEC (cart _143061 (finite_sum _143062 _143063))) = (@GSPEC (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@GSPEC (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050847 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term55 _143061 _143062 _143063 f t) = (term94 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050846 _143061 _143062 _143063) (@lem8050845 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050848 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term54 _143061 _143062 _143063 f t) = (term55 _143061 _143062 _143063 f t)) = ((term26 _143061 _143062 _143063 f t) = (term94 _143061 _143062 _143063 f t)).
Proof. exact (MK_COMB (@lem8050827 _143061 _143062 _143063 f t) (@lem8050847 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050849 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term26 _143061 _143062 _143063 f t) = (term94 _143061 _143062 _143063 f t).
Proof. exact (EQ_MP (@lem8050848 _143061 _143062 _143063 f t) (@lem8050812 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050862 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) : (term95 _143061 _143062 _143063 x y) = (term95 _143061 _143062 _143063 x y).
Proof. exact (eq_refl (term95 _143061 _143062 _143063 x y)). Qed.
Lemma lem8050863 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term41 _143061 _143062 _143063 x y f t) = (term96 _143061 _143062 _143063 x y f t).
Proof. exact (MK_COMB (@lem8050862 _143061 _143062 _143063 x y) (@lem8050849 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050865 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem8050705 _83095 p x) (@lem8050704 _83095 p x)). Qed.
Lemma lem8050866 {_143061 _143062 _143063 : Type'} (p : type16 _143061 _143062 _143063) (x : type2 _143061 _143062 _143063) : (term97 _143061 _143062 _143063 x p) = (p x).
Proof. exact (@lem8050865 (type2 _143061 _143062 _143063) p x). Qed.
Lemma lem8050867 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) (x : cart _143061 _143062) (y : cart _143061 _143063) : (term98 _143061 _143062 _143063 x y f t) = (term99 _143061 _143062 _143063 f t x y).
Proof. exact (@lem8050866 _143061 _143062 _143063 (term100 _143061 _143062 _143063 f t) (@pastecart _143061 _143062 _143063 x y)). Qed.
Lemma lem8050868 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term101 _143061 _143062 _143063 f t a) = (term83 _143061 _143062 _143063 f a t).
Proof. exact (eq_refl (term101 _143061 _143062 _143063 f t a)). Qed.
Lemma lem8050869 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) : (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56) = (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _143061 (finite_sum _143062 _143063)) GEN_PVAR_56)). Qed.
Lemma lem8050870 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (a : type2 _143061 _143062 _143063) (t : type24 _143061 _143063) : (term102 _143061 _143062 _143063 GEN_PVAR_56 f t a) = (term85 _143061 _143062 _143063 GEN_PVAR_56 f a t).
Proof. exact (MK_COMB (@lem8050869 _143061 _143062 _143063 GEN_PVAR_56) (@lem8050868 _143061 _143062 _143063 f a t)). Qed.
Lemma lem8050871 {_143061 _143062 _143063 : Type'} (a : type2 _143061 _143062 _143063) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8050872 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) (a : type2 _143061 _143062 _143063) : (term103 _143061 _143062 _143063 GEN_PVAR_56 f t a) = (term87 _143061 _143062 _143063 GEN_PVAR_56 f t a).
Proof. exact (MK_COMB (@lem8050870 _143061 _143062 _143063 GEN_PVAR_56 f a t) (@lem8050871 _143061 _143062 _143063 a)). Qed.
Lemma lem8050873 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term104 _143061 _143062 _143063 GEN_PVAR_56 f t) = (term89 _143061 _143062 _143063 GEN_PVAR_56 f t).
Proof. exact (fun_ext (fun a : type2 _143061 _143062 _143063 => @lem8050872 _143061 _143062 _143063 GEN_PVAR_56 f t a)). Qed.
Lemma lem8050874 {_143061 _143062 _143063 : Type'} : (@ex (cart _143061 (finite_sum _143062 _143063))) = (@ex (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@ex (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050875 {_143061 _143062 _143063 : Type'} (GEN_PVAR_56 : type2 _143061 _143062 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term105 _143061 _143062 _143063 GEN_PVAR_56 f t) = (term91 _143061 _143062 _143063 GEN_PVAR_56 f t).
Proof. exact (MK_COMB (@lem8050874 _143061 _143062 _143063) (@lem8050873 _143061 _143062 _143063 GEN_PVAR_56 f t)). Qed.
Lemma lem8050876 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term106 _143061 _143062 _143063 f t) = (term93 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _143061 _143062 _143063 => @lem8050875 _143061 _143062 _143063 GEN_PVAR_56 f t)). Qed.
Lemma lem8050877 {_143061 _143062 _143063 : Type'} : (@GSPEC (cart _143061 (finite_sum _143062 _143063))) = (@GSPEC (cart _143061 (finite_sum _143062 _143063))).
Proof. exact (eq_refl (@GSPEC (cart _143061 (finite_sum _143062 _143063)))). Qed.
Lemma lem8050878 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term107 _143061 _143062 _143063 f t) = (term94 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050877 _143061 _143062 _143063) (@lem8050876 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050879 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) : (term95 _143061 _143062 _143063 x y) = (term95 _143061 _143062 _143063 x y).
Proof. exact (eq_refl (term95 _143061 _143062 _143063 x y)). Qed.
Lemma lem8050880 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term98 _143061 _143062 _143063 x y f t) = (term96 _143061 _143062 _143063 x y f t).
Proof. exact (MK_COMB (@lem8050879 _143061 _143062 _143063 x y) (@lem8050878 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050882 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (y : cart _143061 _143063) (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term108 _143061 _143062 _143063 x y f t) = (term109 _143061 _143062 _143063 x y f t).
Proof. exact (MK_COMB (@lem8050881) (@lem8050880 _143061 _143062 _143063 x y f t)). Qed.
Lemma lem8050883 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term99 _143061 _143062 _143063 f t x y) = (term110 _143061 _143062 _143063 f x y t).
Proof. exact (eq_refl (term99 _143061 _143062 _143063 f t x y)). Qed.
Lemma lem8050884 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : ((term98 _143061 _143062 _143063 x y f t) = (term99 _143061 _143062 _143063 f t x y)) = ((term96 _143061 _143062 _143063 x y f t) = (term110 _143061 _143062 _143063 f x y t)).
Proof. exact (MK_COMB (@lem8050882 _143061 _143062 _143063 x y f t) (@lem8050883 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050885 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term96 _143061 _143062 _143063 x y f t) = (term110 _143061 _143062 _143063 f x y t).
Proof. exact (EQ_MP (@lem8050884 _143061 _143062 _143063 f x y t) (@lem8050867 _143061 _143062 _143063 f t x y)). Qed.
Lemma lem8050895 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050674 _141927 _141928 _141929 x s y t) (@lem8050673 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050896 {_143061 _143062 _143063 : Type'} (x : cart _143061 _143062) (s : type24 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term7 _143061 _143062 _143063 x y s t) = (term8 _143061 _143062 _143063 x s y t).
Proof. exact (@lem8050895 _143061 _143062 _143063 x s y t). Qed.
Lemma lem8050899 {_143061 _143062 : Type'} (s : type24 _143061 _143062) (f : type56 _143061 _143062) : (term75 _143061 _143062 s f) = (term75 _143061 _143062 s f).
Proof. exact (eq_refl (term75 _143061 _143062 s f)). Qed.
Lemma lem8050900 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (s : type24 _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term111 _143061 _143062 _143063 f x y s t) = (term112 _143061 _143062 _143063 f x s y t).
Proof. exact (MK_COMB (@lem8050899 _143061 _143062 s f) (@lem8050896 _143061 _143062 _143063 x s y t)). Qed.
Lemma lem8050903 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term113 _143061 _143062 _143063 f x y t) = (term114 _143061 _143062 _143063 f x y t).
Proof. exact (fun_ext (fun s : type24 _143061 _143062 => @lem8050900 _143061 _143062 _143063 f x s y t)). Qed.
Lemma lem8050904 {_143061 _143062 : Type'} : (@all ((cart _143061 _143062) -> Prop)) = (@all ((cart _143061 _143062) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143061 _143062) -> Prop))). Qed.
Lemma lem8050905 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term110 _143061 _143062 _143063 f x y t) = (term115 _143061 _143062 _143063 f x y t).
Proof. exact (MK_COMB (@lem8050904 _143061 _143062) (@lem8050903 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050912 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term96 _143061 _143062 _143063 x y f t) = (term115 _143061 _143062 _143063 f x y t).
Proof. exact (TRANS (@lem8050885 _143061 _143062 _143063 f x y t) (@lem8050905 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050913 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : (term41 _143061 _143062 _143063 x y f t) = (term115 _143061 _143062 _143063 f x y t).
Proof. exact (TRANS (@lem8050863 _143061 _143062 _143063 x y f t) (@lem8050912 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050914 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (y : cart _143061 _143063) (t : type24 _143061 _143063) : ((term40 _143061 _143062 _143063 x y f t) = (term41 _143061 _143062 _143063 x y f t)) = ((term49 _143061 _143062 _143063 x f y t) = (term115 _143061 _143062 _143063 f x y t)).
Proof. exact (MK_COMB (@lem8050808 _143061 _143062 _143063 x f y t) (@lem8050913 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050919 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term43 _143061 _143062 _143063 x f t) = (term116 _143061 _143062 _143063 f x t).
Proof. exact (fun_ext (fun y : cart _143061 _143063 => @lem8050914 _143061 _143062 _143063 f x y t)). Qed.
Lemma lem8050920 {_143061 _143063 : Type'} : (@all (cart _143061 _143063)) = (@all (cart _143061 _143063)).
Proof. exact (eq_refl (@all (cart _143061 _143063))). Qed.
Lemma lem8050921 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (x : cart _143061 _143062) (t : type24 _143061 _143063) : (term45 _143061 _143062 _143063 x f t) = (term117 _143061 _143062 _143063 f x t).
Proof. exact (MK_COMB (@lem8050920 _143061 _143063) (@lem8050919 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8050928 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term47 _143061 _143062 _143063 f t) = (term118 _143061 _143062 _143063 f t).
Proof. exact (fun_ext (fun x : cart _143061 _143062 => @lem8050921 _143061 _143062 _143063 f x t)). Qed.
Lemma lem8050929 {_143061 _143062 : Type'} : (@all (cart _143061 _143062)) = (@all (cart _143061 _143062)).
Proof. exact (eq_refl (@all (cart _143061 _143062))). Qed.
Lemma lem8050930 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term48 _143061 _143062 _143063 f t) = (term119 _143061 _143062 _143063 f t).
Proof. exact (MK_COMB (@lem8050929 _143061 _143062) (@lem8050928 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050937 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : ((term25 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t)) = (term119 _143061 _143062 _143063 f t).
Proof. exact (TRANS (@lem8050790 _143061 _143062 _143063 f t) (@lem8050930 _143061 _143062 _143063 f t)). Qed.
Lemma lem8050938 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) (t : type24 _143061 _143063) : (term119 _143061 _143062 _143063 f t) = ((term25 _143061 _143062 _143063 f t) = (term26 _143061 _143062 _143063 f t)).
Proof. exact (SYM (@lem8050937 _143061 _143062 _143063 f t)). Qed.
