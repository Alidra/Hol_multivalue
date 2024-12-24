Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8050018_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464394_spec.
Require Import thm3464397_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8049694 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8049695 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8049696 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8049695 _141927 _141928 _141929 s) (@lem8049694 _141927 _141928 _141929 s)). Qed.
Lemma lem8049697 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8049696 _141927 _141928 _141929 s t). Qed.
Lemma lem8049698 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049699 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8049698 _141927 _141928 _141929 s t) (@lem8049697 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049700 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8049699 _141927 _141928 _141929 s t x). Qed.
Lemma lem8049701 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049702 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8049701 _141927 _141928 _141929 x s t) (@lem8049700 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049703 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8049702 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8049704 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049730 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem8049731 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem8049730 _83095 p). Qed.
Lemma lem8049732 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem8049733 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem8049732 _83095 p) (@lem8049731 _83095 p)). Qed.
Lemma lem8049734 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem8049733 _83095 p x). Qed.
Lemma lem8049735 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem8049744 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8049745 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8049746 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8049745 A s) (@lem8049744 A s)). Qed.
Lemma lem8049747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8049746 A s t). Qed.
Lemma lem8049748 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8049758 {_89769 _89788 _89789 : Type'} : term18 _89769 _89788 _89789.
Proof. exact (EQ_MP (@lem3464397 _89769 _89788 _89789) (@lem3464394 _89769 _89788 _89789)). Qed.
Lemma lem8049759 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : term19 _89769 _89788 _89789 P.
Proof. exact (@lem8049758 _89769 _89788 _89789 P). Qed.
Lemma lem8049760 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : (term19 _89769 _89788 _89789 P) = (term20 _89769 _89788 _89789 P).
Proof. exact (eq_refl (term19 _89769 _89788 _89789 P)). Qed.
Lemma lem8049761 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : term20 _89769 _89788 _89789 P.
Proof. exact (EQ_MP (@lem8049760 _89769 _89788 _89789 P) (@lem8049759 _89769 _89788 _89789 P)). Qed.
Lemma lem8049762 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term21 _89769 _89788 _89789 P f.
Proof. exact (@lem8049761 _89769 _89788 _89789 P f). Qed.
Lemma lem8049763 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term21 _89769 _89788 _89789 P f) = ((term22 _89769 _89788 _89789 P f) = (term23 _89769 _89788 _89789 P f)).
Proof. exact (eq_refl (term21 _89769 _89788 _89789 P f)). Qed.
Lemma lem8049801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8049748 A s t) (@lem8049747 A s t)). Qed.
Lemma lem8049802 {_142951 _142952 _142953 : Type'} (s : type16 _142951 _142952 _142953) (t : type16 _142951 _142952 _142953) : (s = t) = (term24 _142951 _142952 _142953 s t).
Proof. exact (@lem8049801 (type2 _142951 _142952 _142953) s t). Qed.
Lemma lem8049803 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f g)) = (term27 _142951 _142952 _142953 f g).
Proof. exact (@lem8049802 _142951 _142952 _142953 (term25 _142951 _142952 _142953 f g) (term26 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049809 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term28 _140454 _140455 _140456 P) = (term29 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8049810 {_142951 _142952 _142953 : Type'} (P : type16 _142951 _142952 _142953) : (term28 _142951 _142952 _142953 P) = (term29 _142951 _142952 _142953 P).
Proof. exact (@lem8049809 _142951 _142952 _142953 P). Qed.
Lemma lem8049811 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term30 _142951 _142952 _142953 f g) = (term31 _142951 _142952 _142953 f g).
Proof. exact (@lem8049810 _142951 _142952 _142953 (term32 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049812 {_142951 _142952 _142953 : Type'} (x : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term33 _142951 _142952 _142953 f g x) = ((term34 _142951 _142952 _142953 x f g) = (term35 _142951 _142952 _142953 x f g)).
Proof. exact (eq_refl (term33 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8049813 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term36 _142951 _142952 _142953 f g) = (term32 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : type2 _142951 _142952 _142953 => @lem8049812 _142951 _142952 _142953 x f g)). Qed.
Lemma lem8049814 {_142951 _142952 _142953 : Type'} : (@all (cart _142951 (finite_sum _142952 _142953))) = (@all (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@all (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049815 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term30 _142951 _142952 _142953 f g) = (term27 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049814 _142951 _142952 _142953) (@lem8049813 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049817 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term37 _142951 _142952 _142953 f g) = (term38 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049816) (@lem8049815 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049818 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term39 _142951 _142952 _142953 f g x y) = ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y f g)).
Proof. exact (eq_refl (term39 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049819 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term42 _142951 _142952 _142953 f g x) = (term43 _142951 _142952 _142953 x f g).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049818 _142951 _142952 _142953 x y f g)). Qed.
Lemma lem8049820 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8049821 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term44 _142951 _142952 _142953 f g x) = (term45 _142951 _142952 _142953 x f g).
Proof. exact (MK_COMB (@lem8049820 _142951 _142953) (@lem8049819 _142951 _142952 _142953 x f g)). Qed.
Lemma lem8049822 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term46 _142951 _142952 _142953 f g) = (term47 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8049821 _142951 _142952 _142953 x f g)). Qed.
Lemma lem8049823 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8049824 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term31 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049823 _142951 _142952) (@lem8049822 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049825 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term30 _142951 _142952 _142953 f g) = (term31 _142951 _142952 _142953 f g)) = ((term27 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g)).
Proof. exact (MK_COMB (@lem8049817 _142951 _142952 _142953 f g) (@lem8049824 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049826 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term27 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8049825 _142951 _142952 _142953 f g) (@lem8049811 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049833 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f g)) = (term48 _142951 _142952 _142953 f g).
Proof. exact (TRANS (@lem8049803 _142951 _142952 _142953 f g) (@lem8049826 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049845 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049704 _141927 _141928 _141929 x s y t) (@lem8049703 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049846 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049845 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049847 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term40 _142951 _142952 _142953 x y f g) = (term49 _142951 _142952 _142953 x f y g).
Proof. exact (@lem8049846 _142951 _142952 _142953 x (@INTERS (cart _142951 _142952) f) y (@INTERS (cart _142951 _142953) g)). Qed.
Lemma lem8049850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049851 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term50 _142951 _142952 _142953 x y f g) = (term51 _142951 _142952 _142953 x f y g).
Proof. exact (MK_COMB (@lem8049850) (@lem8049847 _142951 _142952 _142953 x f y g)). Qed.
Lemma lem8049853 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term22 _89769 _89788 _89789 P f) = (term23 _89769 _89788 _89789 P f).
Proof. exact (EQ_MP (@lem8049763 _89769 _89788 _89789 P f) (@lem8049762 _89769 _89788 _89789 P f)). Qed.
Lemma lem8049854 {_142951 _142952 _142953 : Type'} (P : type55 _142951 _142952 _142953) (f : type54 _142951 _142952 _142953) : (term52 _142951 _142952 _142953 P f) = (term53 _142951 _142952 _142953 P f).
Proof. exact (@lem8049853 (type2 _142951 _142952 _142953) (type24 _142951 _142953) (type24 _142951 _142952) P f). Qed.
Lemma lem8049855 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term54 _142951 _142952 _142953 f g) = (term55 _142951 _142952 _142953 f g).
Proof. exact (@lem8049854 _142951 _142952 _142953 (term56 _142951 _142952 _142953 f g) (@PCROSS _142951 _142952 _142953)). Qed.
Lemma lem8049856 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term57 _142951 _142952 _142953 f g s) = (term58 _142951 _142952 _142953 s f g).
Proof. exact (eq_refl (term57 _142951 _142952 _142953 f g s)). Qed.
Lemma lem8049857 {_142951 _142953 : Type'} (t : type24 _142951 _142953) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem8049858 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term59 _142951 _142952 _142953 f g s t) = (term60 _142951 _142952 _142953 s f g t).
Proof. exact (MK_COMB (@lem8049856 _142951 _142952 _142953 s f g) (@lem8049857 _142951 _142953 t)). Qed.
Lemma lem8049859 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term60 _142951 _142952 _142953 s f g t) = (term61 _142951 _142952 _142953 s f t g).
Proof. exact (eq_refl (term60 _142951 _142952 _142953 s f g t)). Qed.
Lemma lem8049860 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term59 _142951 _142952 _142953 f g s t) = (term61 _142951 _142952 _142953 s f t g).
Proof. exact (TRANS (@lem8049858 _142951 _142952 _142953 s f g t) (@lem8049859 _142951 _142952 _142953 s f t g)). Qed.
Lemma lem8049861 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) : (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_367) = (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_367).
Proof. exact (eq_refl (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_367)). Qed.
Lemma lem8049862 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term62 _142951 _142952 _142953 GEN_PVAR_367 f g s t) = (term63 _142951 _142952 _142953 GEN_PVAR_367 s f t g).
Proof. exact (MK_COMB (@lem8049861 _142951 _142952 _142953 GEN_PVAR_367) (@lem8049860 _142951 _142952 _142953 s f t g)). Qed.
Lemma lem8049863 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (t : type24 _142951 _142953) : (@PCROSS _142951 _142952 _142953 s t) = (@PCROSS _142951 _142952 _142953 s t).
Proof. exact (eq_refl (@PCROSS _142951 _142952 _142953 s t)). Qed.
Lemma lem8049864 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) : (term64 _142951 _142952 _142953 GEN_PVAR_367 f g s t) = (term65 _142951 _142952 _142953 GEN_PVAR_367 f g s t).
Proof. exact (MK_COMB (@lem8049862 _142951 _142952 _142953 GEN_PVAR_367 s f t g) (@lem8049863 _142951 _142952 _142953 s t)). Qed.
Lemma lem8049865 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) : (term66 _142951 _142952 _142953 GEN_PVAR_367 f g s) = (term67 _142951 _142952 _142953 GEN_PVAR_367 f g s).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049864 _142951 _142952 _142953 GEN_PVAR_367 f g s t)). Qed.
Lemma lem8049866 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049867 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (s : type24 _142951 _142952) : (term68 _142951 _142952 _142953 GEN_PVAR_367 f g s) = (term69 _142951 _142952 _142953 GEN_PVAR_367 f g s).
Proof. exact (MK_COMB (@lem8049866 _142951 _142953) (@lem8049865 _142951 _142952 _142953 GEN_PVAR_367 f g s)). Qed.
Lemma lem8049868 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term70 _142951 _142952 _142953 GEN_PVAR_367 f g) = (term71 _142951 _142952 _142953 GEN_PVAR_367 f g).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049867 _142951 _142952 _142953 GEN_PVAR_367 f g s)). Qed.
Lemma lem8049869 {_142951 _142952 : Type'} : (@ex ((cart _142951 _142952) -> Prop)) = (@ex ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049870 {_142951 _142952 _142953 : Type'} (GEN_PVAR_367 : type16 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term72 _142951 _142952 _142953 GEN_PVAR_367 f g) = (term73 _142951 _142952 _142953 GEN_PVAR_367 f g).
Proof. exact (MK_COMB (@lem8049869 _142951 _142952) (@lem8049868 _142951 _142952 _142953 GEN_PVAR_367 f g)). Qed.
Lemma lem8049871 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term74 _142951 _142952 _142953 f g) = (term75 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun GEN_PVAR_367 : type16 _142951 _142952 _142953 => @lem8049870 _142951 _142952 _142953 GEN_PVAR_367 f g)). Qed.
Lemma lem8049872 {_142951 _142952 _142953 : Type'} : (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049873 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term76 _142951 _142952 _142953 f g) = (term77 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049872 _142951 _142952 _142953) (@lem8049871 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049874 {_142951 _142952 _142953 : Type'} : (@INTERS (cart _142951 (finite_sum _142952 _142953))) = (@INTERS (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@INTERS (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049875 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term54 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049874 _142951 _142952 _142953) (@lem8049873 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049876 {_142951 _142952 _142953 : Type'} : (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049877 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term78 _142951 _142952 _142953 f g) = (term79 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049876 _142951 _142952 _142953) (@lem8049875 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049878 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term57 _142951 _142952 _142953 f g s) = (term58 _142951 _142952 _142953 s f g).
Proof. exact (eq_refl (term57 _142951 _142952 _142953 f g s)). Qed.
Lemma lem8049879 {_142951 _142953 : Type'} (t : type24 _142951 _142953) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem8049880 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term59 _142951 _142952 _142953 f g s t) = (term60 _142951 _142952 _142953 s f g t).
Proof. exact (MK_COMB (@lem8049878 _142951 _142952 _142953 s f g) (@lem8049879 _142951 _142953 t)). Qed.
Lemma lem8049881 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term60 _142951 _142952 _142953 s f g t) = (term61 _142951 _142952 _142953 s f t g).
Proof. exact (eq_refl (term60 _142951 _142952 _142953 s f g t)). Qed.
Lemma lem8049882 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term59 _142951 _142952 _142953 f g s t) = (term61 _142951 _142952 _142953 s f t g).
Proof. exact (TRANS (@lem8049880 _142951 _142952 _142953 s f g t) (@lem8049881 _142951 _142952 _142953 s f t g)). Qed.
Lemma lem8049883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8049884 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term80 _142951 _142952 _142953 f g s t) = (term81 _142951 _142952 _142953 s f t g).
Proof. exact (MK_COMB (@lem8049883) (@lem8049882 _142951 _142952 _142953 s f t g)). Qed.
Lemma lem8049885 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) : (term82 _142951 _142952 _142953 a s t) = (term82 _142951 _142952 _142953 a s t).
Proof. exact (eq_refl (term82 _142951 _142952 _142953 a s t)). Qed.
Lemma lem8049886 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) (t : type24 _142951 _142953) : (term83 _142951 _142952 _142953 f g a s t) = (term84 _142951 _142952 _142953 f g a s t).
Proof. exact (MK_COMB (@lem8049884 _142951 _142952 _142953 s f t g) (@lem8049885 _142951 _142952 _142953 a s t)). Qed.
Lemma lem8049887 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) : (term85 _142951 _142952 _142953 f g a s) = (term86 _142951 _142952 _142953 f g a s).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049886 _142951 _142952 _142953 f g a s t)). Qed.
Lemma lem8049888 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049889 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) (s : type24 _142951 _142952) : (term87 _142951 _142952 _142953 f g a s) = (term88 _142951 _142952 _142953 f g a s).
Proof. exact (MK_COMB (@lem8049888 _142951 _142953) (@lem8049887 _142951 _142952 _142953 f g a s)). Qed.
Lemma lem8049890 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term89 _142951 _142952 _142953 f g a) = (term90 _142951 _142952 _142953 f g a).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049889 _142951 _142952 _142953 f g a s)). Qed.
Lemma lem8049891 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049892 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term91 _142951 _142952 _142953 f g a) = (term92 _142951 _142952 _142953 f g a).
Proof. exact (MK_COMB (@lem8049891 _142951 _142952) (@lem8049890 _142951 _142952 _142953 f g a)). Qed.
Lemma lem8049893 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58)). Qed.
Lemma lem8049894 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term93 _142951 _142952 _142953 GEN_PVAR_58 f g a) = (term94 _142951 _142952 _142953 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem8049893 _142951 _142952 _142953 GEN_PVAR_58) (@lem8049892 _142951 _142952 _142953 f g a)). Qed.
Lemma lem8049895 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049896 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term95 _142951 _142952 _142953 GEN_PVAR_58 f g a) = (term96 _142951 _142952 _142953 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem8049894 _142951 _142952 _142953 GEN_PVAR_58 f g a) (@lem8049895 _142951 _142952 _142953 a)). Qed.
Lemma lem8049897 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term97 _142951 _142952 _142953 GEN_PVAR_58 f g) = (term98 _142951 _142952 _142953 GEN_PVAR_58 f g).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049896 _142951 _142952 _142953 GEN_PVAR_58 f g a)). Qed.
Lemma lem8049898 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049899 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term99 _142951 _142952 _142953 GEN_PVAR_58 f g) = (term100 _142951 _142952 _142953 GEN_PVAR_58 f g).
Proof. exact (MK_COMB (@lem8049898 _142951 _142952 _142953) (@lem8049897 _142951 _142952 _142953 GEN_PVAR_58 f g)). Qed.
Lemma lem8049900 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term101 _142951 _142952 _142953 f g) = (term102 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun GEN_PVAR_58 : type2 _142951 _142952 _142953 => @lem8049899 _142951 _142952 _142953 GEN_PVAR_58 f g)). Qed.
Lemma lem8049901 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049902 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term55 _142951 _142952 _142953 f g) = (term103 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049901 _142951 _142952 _142953) (@lem8049900 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049903 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term54 _142951 _142952 _142953 f g) = (term55 _142951 _142952 _142953 f g)) = ((term26 _142951 _142952 _142953 f g) = (term103 _142951 _142952 _142953 f g)).
Proof. exact (MK_COMB (@lem8049877 _142951 _142952 _142953 f g) (@lem8049902 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049904 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term26 _142951 _142952 _142953 f g) = (term103 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8049903 _142951 _142952 _142953 f g) (@lem8049855 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049925 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term104 _142951 _142952 _142953 x y) = (term104 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term104 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049926 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term41 _142951 _142952 _142953 x y f g) = (term105 _142951 _142952 _142953 x y f g).
Proof. exact (MK_COMB (@lem8049925 _142951 _142952 _142953 x y) (@lem8049904 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049928 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem8049735 _83095 p x) (@lem8049734 _83095 p x)). Qed.
Lemma lem8049929 {_142951 _142952 _142953 : Type'} (p : type16 _142951 _142952 _142953) (x : type2 _142951 _142952 _142953) : (term106 _142951 _142952 _142953 x p) = (p x).
Proof. exact (@lem8049928 (type2 _142951 _142952 _142953) p x). Qed.
Lemma lem8049930 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term107 _142951 _142952 _142953 x y f g) = (term108 _142951 _142952 _142953 f g x y).
Proof. exact (@lem8049929 _142951 _142952 _142953 (term109 _142951 _142952 _142953 f g) (@pastecart _142951 _142952 _142953 x y)). Qed.
Lemma lem8049931 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term110 _142951 _142952 _142953 f g a) = (term92 _142951 _142952 _142953 f g a).
Proof. exact (eq_refl (term110 _142951 _142952 _142953 f g a)). Qed.
Lemma lem8049932 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_58)). Qed.
Lemma lem8049933 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term111 _142951 _142952 _142953 GEN_PVAR_58 f g a) = (term94 _142951 _142952 _142953 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem8049932 _142951 _142952 _142953 GEN_PVAR_58) (@lem8049931 _142951 _142952 _142953 f g a)). Qed.
Lemma lem8049934 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049935 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term112 _142951 _142952 _142953 GEN_PVAR_58 f g a) = (term96 _142951 _142952 _142953 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem8049933 _142951 _142952 _142953 GEN_PVAR_58 f g a) (@lem8049934 _142951 _142952 _142953 a)). Qed.
Lemma lem8049936 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term113 _142951 _142952 _142953 GEN_PVAR_58 f g) = (term98 _142951 _142952 _142953 GEN_PVAR_58 f g).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049935 _142951 _142952 _142953 GEN_PVAR_58 f g a)). Qed.
Lemma lem8049937 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049938 {_142951 _142952 _142953 : Type'} (GEN_PVAR_58 : type2 _142951 _142952 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term114 _142951 _142952 _142953 GEN_PVAR_58 f g) = (term100 _142951 _142952 _142953 GEN_PVAR_58 f g).
Proof. exact (MK_COMB (@lem8049937 _142951 _142952 _142953) (@lem8049936 _142951 _142952 _142953 GEN_PVAR_58 f g)). Qed.
Lemma lem8049939 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term115 _142951 _142952 _142953 f g) = (term102 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun GEN_PVAR_58 : type2 _142951 _142952 _142953 => @lem8049938 _142951 _142952 _142953 GEN_PVAR_58 f g)). Qed.
Lemma lem8049940 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049941 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term116 _142951 _142952 _142953 f g) = (term103 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049940 _142951 _142952 _142953) (@lem8049939 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049942 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term104 _142951 _142952 _142953 x y) = (term104 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term104 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049943 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term107 _142951 _142952 _142953 x y f g) = (term105 _142951 _142952 _142953 x y f g).
Proof. exact (MK_COMB (@lem8049942 _142951 _142952 _142953 x y) (@lem8049941 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049945 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term117 _142951 _142952 _142953 x y f g) = (term118 _142951 _142952 _142953 x y f g).
Proof. exact (MK_COMB (@lem8049944) (@lem8049943 _142951 _142952 _142953 x y f g)). Qed.
Lemma lem8049946 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term108 _142951 _142952 _142953 f g x y) = (term119 _142951 _142952 _142953 f g x y).
Proof. exact (eq_refl (term108 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049947 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term107 _142951 _142952 _142953 x y f g) = (term108 _142951 _142952 _142953 f g x y)) = ((term105 _142951 _142952 _142953 x y f g) = (term119 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8049945 _142951 _142952 _142953 x y f g) (@lem8049946 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049948 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term105 _142951 _142952 _142953 x y f g) = (term119 _142951 _142952 _142953 f g x y).
Proof. exact (EQ_MP (@lem8049947 _142951 _142952 _142953 f g x y) (@lem8049930 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049966 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049704 _141927 _141928 _141929 x s y t) (@lem8049703 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049967 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049966 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049970 {_142951 _142952 _142953 : Type'} (s : type24 _142951 _142952) (f : type56 _142951 _142952) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term81 _142951 _142952 _142953 s f t g) = (term81 _142951 _142952 _142953 s f t g).
Proof. exact (eq_refl (term81 _142951 _142952 _142953 s f t g)). Qed.
Lemma lem8049971 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term120 _142951 _142952 _142953 f g x y s t) = (term121 _142951 _142952 _142953 f g x s y t).
Proof. exact (MK_COMB (@lem8049970 _142951 _142952 _142953 s f t g) (@lem8049967 _142951 _142952 _142953 x s y t)). Qed.
Lemma lem8049974 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) : (term122 _142951 _142952 _142953 f g x y s) = (term123 _142951 _142952 _142953 f g x s y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049971 _142951 _142952 _142953 f g x s y t)). Qed.
Lemma lem8049975 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049976 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) : (term124 _142951 _142952 _142953 f g x y s) = (term125 _142951 _142952 _142953 f g x s y).
Proof. exact (MK_COMB (@lem8049975 _142951 _142953) (@lem8049974 _142951 _142952 _142953 f g x s y)). Qed.
Lemma lem8049983 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term126 _142951 _142952 _142953 f g x y) = (term127 _142951 _142952 _142953 f g x y).
Proof. exact (fun_ext (fun s : type24 _142951 _142952 => @lem8049976 _142951 _142952 _142953 f g x s y)). Qed.
Lemma lem8049984 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8049985 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term119 _142951 _142952 _142953 f g x y) = (term128 _142951 _142952 _142953 f g x y).
Proof. exact (MK_COMB (@lem8049984 _142951 _142952) (@lem8049983 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049992 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term105 _142951 _142952 _142953 x y f g) = (term128 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8049948 _142951 _142952 _142953 f g x y) (@lem8049985 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049993 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term41 _142951 _142952 _142953 x y f g) = (term128 _142951 _142952 _142953 f g x y).
Proof. exact (TRANS (@lem8049926 _142951 _142952 _142953 x y f g) (@lem8049992 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049994 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y f g)) = ((term49 _142951 _142952 _142953 x f y g) = (term128 _142951 _142952 _142953 f g x y)).
Proof. exact (MK_COMB (@lem8049851 _142951 _142952 _142953 x f y g) (@lem8049993 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049999 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term43 _142951 _142952 _142953 x f g) = (term129 _142951 _142952 _142953 f g x).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049994 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8050000 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8050001 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term45 _142951 _142952 _142953 x f g) = (term130 _142951 _142952 _142953 f g x).
Proof. exact (MK_COMB (@lem8050000 _142951 _142953) (@lem8049999 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8050008 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term47 _142951 _142952 _142953 f g) = (term131 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8050001 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8050009 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8050010 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term48 _142951 _142952 _142953 f g) = (term132 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8050009 _142951 _142952) (@lem8050008 _142951 _142952 _142953 f g)). Qed.
Lemma lem8050017 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f g)) = (term132 _142951 _142952 _142953 f g).
Proof. exact (TRANS (@lem8049833 _142951 _142952 _142953 f g) (@lem8050010 _142951 _142952 _142953 f g)). Qed.
Lemma lem8050018 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term132 _142951 _142952 _142953 f g) = ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 f g)).
Proof. exact (SYM (@lem8050017 _142951 _142952 _142953 f g)). Qed.
