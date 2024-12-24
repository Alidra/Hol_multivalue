Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8003920_term_abbrevs.
Require Import FORALL_IN_GSPEC_spec.
Require Import PCROSS_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8003768 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term0 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem8003784 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term1 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem8003768 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem8003785 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term2 _88961 _88962 _89106 Q P.
Proof. exact (@lem8003784 _88961 _88962 _89106 Q P). Qed.
Lemma lem8003786 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term2 _88961 _88962 _89106 Q P) = (term3 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term2 _88961 _88962 _89106 Q P)). Qed.
Lemma lem8003787 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term3 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem8003786 _88961 _88962 _89106 P Q) (@lem8003785 _88961 _88962 _89106 Q P)). Qed.
Lemma lem8003788 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term4 _88961 _88962 _89106 P Q f.
Proof. exact (@lem8003787 _88961 _88962 _89106 P Q f). Qed.
Lemma lem8003789 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term4 _88961 _88962 _89106 P Q f) = ((term5 _88961 _88962 _89106 P f Q) = (term6 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term4 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem8003798 {A M N : Type'} (s : type24 A M) : term7 A M N s.
Proof. exact (@lem8003767 A M N s). Qed.
Lemma lem8003799 {A M N : Type'} (s : type24 A M) : (term7 A M N s) = (term8 A M N s).
Proof. exact (eq_refl (term7 A M N s)). Qed.
Lemma lem8003800 {A M N : Type'} (s : type24 A M) : term8 A M N s.
Proof. exact (EQ_MP (@lem8003799 A M N s) (@lem8003798 A M N s)). Qed.
Lemma lem8003801 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term9 A M N s t.
Proof. exact (@lem8003800 A M N s t). Qed.
Lemma lem8003802 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term9 A M N s t) = ((@PCROSS A M N s t) = (term10 A M N s t)).
Proof. exact (eq_refl (term9 A M N s t)). Qed.
Lemma lem8003813 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (term10 A M N s t).
Proof. exact (EQ_MP (@lem8003802 A M N s t) (@lem8003801 A M N s t)). Qed.
Lemma lem8003814 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (@PCROSS _141853 _141854 _141855 s t) = (term10 _141853 _141854 _141855 s t).
Proof. exact (@lem8003813 _141853 _141854 _141855 s t). Qed.
Lemma lem8003825 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) : (@IN (cart _141853 (finite_sum _141854 _141855)) z) = (@IN (cart _141853 (finite_sum _141854 _141855)) z).
Proof. exact (eq_refl (@IN (cart _141853 (finite_sum _141854 _141855)) z)). Qed.
Lemma lem8003826 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term11 _141853 _141854 _141855 z s t) = (term12 _141853 _141854 _141855 z s t).
Proof. exact (MK_COMB (@lem8003825 _141853 _141854 _141855 z) (@lem8003814 _141853 _141854 _141855 s t)). Qed.
Lemma lem8003827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8003828 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term13 _141853 _141854 _141855 z s t) = (term14 _141853 _141854 _141855 z s t).
Proof. exact (MK_COMB (@lem8003827) (@lem8003826 _141853 _141854 _141855 z s t)). Qed.
Lemma lem8003829 {_141853 _141854 _141855 : Type'} (P : type16 _141853 _141854 _141855) (z : type2 _141853 _141854 _141855) : (P z) = (P z).
Proof. exact (eq_refl (P z)). Qed.
Lemma lem8003830 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) (z : type2 _141853 _141854 _141855) : (term15 _141853 _141854 _141855 s t P z) = (term16 _141853 _141854 _141855 s t P z).
Proof. exact (MK_COMB (@lem8003828 _141853 _141854 _141855 z s t) (@lem8003829 _141853 _141854 _141855 P z)). Qed.
Lemma lem8003833 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term17 _141853 _141854 _141855 s t P) = (term18 _141853 _141854 _141855 s t P).
Proof. exact (fun_ext (fun z : type2 _141853 _141854 _141855 => @lem8003830 _141853 _141854 _141855 s t P z)). Qed.
Lemma lem8003834 {_141853 _141854 _141855 : Type'} : (@all (cart _141853 (finite_sum _141854 _141855))) = (@all (cart _141853 (finite_sum _141854 _141855))).
Proof. exact (eq_refl (@all (cart _141853 (finite_sum _141854 _141855)))). Qed.
Lemma lem8003835 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term19 _141853 _141854 _141855 s t P) = (term20 _141853 _141854 _141855 s t P).
Proof. exact (MK_COMB (@lem8003834 _141853 _141854 _141855) (@lem8003833 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003837 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term5 _88961 _88962 _89106 P f Q) = (term6 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem8003789 _88961 _88962 _89106 P Q f) (@lem8003788 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem8003838 {_141853 _141854 _141855 : Type'} (P : type22 _141853 _141854 _141855) (Q : type16 _141853 _141854 _141855) (f : type20 _141853 _141854 _141855) : (term21 _141853 _141854 _141855 P f Q) = (term22 _141853 _141854 _141855 P Q f).
Proof. exact (@lem8003837 (cart _141853 _141855) (cart _141853 _141854) (type2 _141853 _141854 _141855) P Q f). Qed.
Lemma lem8003839 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term23 _141853 _141854 _141855 s t P) = (term24 _141853 _141854 _141855 s t P).
Proof. exact (@lem8003838 _141853 _141854 _141855 (term25 _141853 _141854 _141855 s t) P (@pastecart _141853 _141854 _141855)). Qed.
Lemma lem8003840 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term26 _141853 _141854 _141855 s t x) = (term27 _141853 _141854 _141855 x s t).
Proof. exact (eq_refl (term26 _141853 _141854 _141855 s t x)). Qed.
Lemma lem8003841 {_141853 _141855 : Type'} (y : cart _141853 _141855) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8003842 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (t : type24 _141853 _141855) (y : cart _141853 _141855) : (term28 _141853 _141854 _141855 s t x y) = (term29 _141853 _141854 _141855 x s t y).
Proof. exact (MK_COMB (@lem8003840 _141853 _141854 _141855 x s t) (@lem8003841 _141853 _141855 y)). Qed.
Lemma lem8003843 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term29 _141853 _141854 _141855 x s t y) = (term30 _141853 _141854 _141855 x s y t).
Proof. exact (eq_refl (term29 _141853 _141854 _141855 x s t y)). Qed.
Lemma lem8003844 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term28 _141853 _141854 _141855 s t x y) = (term30 _141853 _141854 _141855 x s y t).
Proof. exact (TRANS (@lem8003842 _141853 _141854 _141855 x s t y) (@lem8003843 _141853 _141854 _141855 x s y t)). Qed.
Lemma lem8003845 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) : (@SETSPEC (cart _141853 (finite_sum _141854 _141855)) GEN_PVAR_361) = (@SETSPEC (cart _141853 (finite_sum _141854 _141855)) GEN_PVAR_361).
Proof. exact (eq_refl (@SETSPEC (cart _141853 (finite_sum _141854 _141855)) GEN_PVAR_361)). Qed.
Lemma lem8003846 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term31 _141853 _141854 _141855 GEN_PVAR_361 s t x y) = (term32 _141853 _141854 _141855 GEN_PVAR_361 x s y t).
Proof. exact (MK_COMB (@lem8003845 _141853 _141854 _141855 GEN_PVAR_361) (@lem8003844 _141853 _141854 _141855 x s y t)). Qed.
Lemma lem8003847 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (y : cart _141853 _141855) : (@pastecart _141853 _141854 _141855 x y) = (@pastecart _141853 _141854 _141855 x y).
Proof. exact (eq_refl (@pastecart _141853 _141854 _141855 x y)). Qed.
Lemma lem8003848 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) (x : cart _141853 _141854) (y : cart _141853 _141855) : (term33 _141853 _141854 _141855 GEN_PVAR_361 s t x y) = (term34 _141853 _141854 _141855 GEN_PVAR_361 s t x y).
Proof. exact (MK_COMB (@lem8003846 _141853 _141854 _141855 GEN_PVAR_361 x s y t) (@lem8003847 _141853 _141854 _141855 x y)). Qed.
Lemma lem8003849 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) (x : cart _141853 _141854) : (term35 _141853 _141854 _141855 GEN_PVAR_361 s t x) = (term36 _141853 _141854 _141855 GEN_PVAR_361 s t x).
Proof. exact (fun_ext (fun y : cart _141853 _141855 => @lem8003848 _141853 _141854 _141855 GEN_PVAR_361 s t x y)). Qed.
Lemma lem8003850 {_141853 _141855 : Type'} : (@ex (cart _141853 _141855)) = (@ex (cart _141853 _141855)).
Proof. exact (eq_refl (@ex (cart _141853 _141855))). Qed.
Lemma lem8003851 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) (x : cart _141853 _141854) : (term37 _141853 _141854 _141855 GEN_PVAR_361 s t x) = (term38 _141853 _141854 _141855 GEN_PVAR_361 s t x).
Proof. exact (MK_COMB (@lem8003850 _141853 _141855) (@lem8003849 _141853 _141854 _141855 GEN_PVAR_361 s t x)). Qed.
Lemma lem8003852 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term39 _141853 _141854 _141855 GEN_PVAR_361 s t) = (term40 _141853 _141854 _141855 GEN_PVAR_361 s t).
Proof. exact (fun_ext (fun x : cart _141853 _141854 => @lem8003851 _141853 _141854 _141855 GEN_PVAR_361 s t x)). Qed.
Lemma lem8003853 {_141853 _141854 : Type'} : (@ex (cart _141853 _141854)) = (@ex (cart _141853 _141854)).
Proof. exact (eq_refl (@ex (cart _141853 _141854))). Qed.
Lemma lem8003854 {_141853 _141854 _141855 : Type'} (GEN_PVAR_361 : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term41 _141853 _141854 _141855 GEN_PVAR_361 s t) = (term42 _141853 _141854 _141855 GEN_PVAR_361 s t).
Proof. exact (MK_COMB (@lem8003853 _141853 _141854) (@lem8003852 _141853 _141854 _141855 GEN_PVAR_361 s t)). Qed.
Lemma lem8003855 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term43 _141853 _141854 _141855 s t) = (term44 _141853 _141854 _141855 s t).
Proof. exact (fun_ext (fun GEN_PVAR_361 : type2 _141853 _141854 _141855 => @lem8003854 _141853 _141854 _141855 GEN_PVAR_361 s t)). Qed.
Lemma lem8003856 {_141853 _141854 _141855 : Type'} : (@GSPEC (cart _141853 (finite_sum _141854 _141855))) = (@GSPEC (cart _141853 (finite_sum _141854 _141855))).
Proof. exact (eq_refl (@GSPEC (cart _141853 (finite_sum _141854 _141855)))). Qed.
Lemma lem8003857 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term45 _141853 _141854 _141855 s t) = (term10 _141853 _141854 _141855 s t).
Proof. exact (MK_COMB (@lem8003856 _141853 _141854 _141855) (@lem8003855 _141853 _141854 _141855 s t)). Qed.
Lemma lem8003858 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) : (@IN (cart _141853 (finite_sum _141854 _141855)) z) = (@IN (cart _141853 (finite_sum _141854 _141855)) z).
Proof. exact (eq_refl (@IN (cart _141853 (finite_sum _141854 _141855)) z)). Qed.
Lemma lem8003859 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term46 _141853 _141854 _141855 z s t) = (term12 _141853 _141854 _141855 z s t).
Proof. exact (MK_COMB (@lem8003858 _141853 _141854 _141855 z) (@lem8003857 _141853 _141854 _141855 s t)). Qed.
Lemma lem8003860 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8003861 {_141853 _141854 _141855 : Type'} (z : type2 _141853 _141854 _141855) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term47 _141853 _141854 _141855 z s t) = (term14 _141853 _141854 _141855 z s t).
Proof. exact (MK_COMB (@lem8003860) (@lem8003859 _141853 _141854 _141855 z s t)). Qed.
Lemma lem8003862 {_141853 _141854 _141855 : Type'} (P : type16 _141853 _141854 _141855) (z : type2 _141853 _141854 _141855) : (P z) = (P z).
Proof. exact (eq_refl (P z)). Qed.
Lemma lem8003863 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) (z : type2 _141853 _141854 _141855) : (term48 _141853 _141854 _141855 s t P z) = (term16 _141853 _141854 _141855 s t P z).
Proof. exact (MK_COMB (@lem8003861 _141853 _141854 _141855 z s t) (@lem8003862 _141853 _141854 _141855 P z)). Qed.
Lemma lem8003864 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term49 _141853 _141854 _141855 s t P) = (term18 _141853 _141854 _141855 s t P).
Proof. exact (fun_ext (fun z : type2 _141853 _141854 _141855 => @lem8003863 _141853 _141854 _141855 s t P z)). Qed.
Lemma lem8003865 {_141853 _141854 _141855 : Type'} : (@all (cart _141853 (finite_sum _141854 _141855))) = (@all (cart _141853 (finite_sum _141854 _141855))).
Proof. exact (eq_refl (@all (cart _141853 (finite_sum _141854 _141855)))). Qed.
Lemma lem8003866 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term23 _141853 _141854 _141855 s t P) = (term20 _141853 _141854 _141855 s t P).
Proof. exact (MK_COMB (@lem8003865 _141853 _141854 _141855) (@lem8003864 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8003868 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term50 _141853 _141854 _141855 s t P) = (term51 _141853 _141854 _141855 s t P).
Proof. exact (MK_COMB (@lem8003867) (@lem8003866 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003869 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (t : type24 _141853 _141855) : (term26 _141853 _141854 _141855 s t x) = (term27 _141853 _141854 _141855 x s t).
Proof. exact (eq_refl (term26 _141853 _141854 _141855 s t x)). Qed.
Lemma lem8003870 {_141853 _141855 : Type'} (y : cart _141853 _141855) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8003871 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (t : type24 _141853 _141855) (y : cart _141853 _141855) : (term28 _141853 _141854 _141855 s t x y) = (term29 _141853 _141854 _141855 x s t y).
Proof. exact (MK_COMB (@lem8003869 _141853 _141854 _141855 x s t) (@lem8003870 _141853 _141855 y)). Qed.
Lemma lem8003872 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term29 _141853 _141854 _141855 x s t y) = (term30 _141853 _141854 _141855 x s y t).
Proof. exact (eq_refl (term29 _141853 _141854 _141855 x s t y)). Qed.
Lemma lem8003873 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term28 _141853 _141854 _141855 s t x y) = (term30 _141853 _141854 _141855 x s y t).
Proof. exact (TRANS (@lem8003871 _141853 _141854 _141855 x s t y) (@lem8003872 _141853 _141854 _141855 x s y t)). Qed.
Lemma lem8003874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8003875 {_141853 _141854 _141855 : Type'} (x : cart _141853 _141854) (s : type24 _141853 _141854) (y : cart _141853 _141855) (t : type24 _141853 _141855) : (term52 _141853 _141854 _141855 s t x y) = (term53 _141853 _141854 _141855 x s y t).
Proof. exact (MK_COMB (@lem8003874) (@lem8003873 _141853 _141854 _141855 x s y t)). Qed.
Lemma lem8003876 {_141853 _141854 _141855 : Type'} (P : type16 _141853 _141854 _141855) (x : cart _141853 _141854) (y : cart _141853 _141855) : (term54 _141853 _141854 _141855 P x y) = (term54 _141853 _141854 _141855 P x y).
Proof. exact (eq_refl (term54 _141853 _141854 _141855 P x y)). Qed.
Lemma lem8003877 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) (x : cart _141853 _141854) (y : cart _141853 _141855) : (term55 _141853 _141854 _141855 s t P x y) = (term56 _141853 _141854 _141855 s t P x y).
Proof. exact (MK_COMB (@lem8003875 _141853 _141854 _141855 x s y t) (@lem8003876 _141853 _141854 _141855 P x y)). Qed.
Lemma lem8003878 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) (x : cart _141853 _141854) : (term57 _141853 _141854 _141855 s t P x) = (term58 _141853 _141854 _141855 s t P x).
Proof. exact (fun_ext (fun y : cart _141853 _141855 => @lem8003877 _141853 _141854 _141855 s t P x y)). Qed.
Lemma lem8003879 {_141853 _141855 : Type'} : (@all (cart _141853 _141855)) = (@all (cart _141853 _141855)).
Proof. exact (eq_refl (@all (cart _141853 _141855))). Qed.
Lemma lem8003880 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) (x : cart _141853 _141854) : (term59 _141853 _141854 _141855 s t P x) = (term60 _141853 _141854 _141855 s t P x).
Proof. exact (MK_COMB (@lem8003879 _141853 _141855) (@lem8003878 _141853 _141854 _141855 s t P x)). Qed.
Lemma lem8003881 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term61 _141853 _141854 _141855 s t P) = (term62 _141853 _141854 _141855 s t P).
Proof. exact (fun_ext (fun x : cart _141853 _141854 => @lem8003880 _141853 _141854 _141855 s t P x)). Qed.
Lemma lem8003882 {_141853 _141854 : Type'} : (@all (cart _141853 _141854)) = (@all (cart _141853 _141854)).
Proof. exact (eq_refl (@all (cart _141853 _141854))). Qed.
Lemma lem8003883 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term24 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P).
Proof. exact (MK_COMB (@lem8003882 _141853 _141854) (@lem8003881 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003884 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : ((term23 _141853 _141854 _141855 s t P) = (term24 _141853 _141854 _141855 s t P)) = ((term20 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)).
Proof. exact (MK_COMB (@lem8003868 _141853 _141854 _141855 s t P) (@lem8003883 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003885 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term20 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P).
Proof. exact (EQ_MP (@lem8003884 _141853 _141854 _141855 s t P) (@lem8003839 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003898 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term19 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P).
Proof. exact (TRANS (@lem8003835 _141853 _141854 _141855 s t P) (@lem8003885 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8003900 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term64 _141853 _141854 _141855 s t P) = (term65 _141853 _141854 _141855 s t P).
Proof. exact (MK_COMB (@lem8003899) (@lem8003898 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003913 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term63 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P).
Proof. exact (eq_refl (term63 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003914 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : ((term19 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)) = ((term63 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)).
Proof. exact (MK_COMB (@lem8003900 _141853 _141854 _141855 s t P) (@lem8003913 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8003917 (x : Prop) : (x = x) = True.
Proof. exact (@lem8003916 Prop x). Qed.
Lemma lem8003918 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : ((term63 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)) = True.
Proof. exact (@lem8003917 (term63 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003919 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : ((term19 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)) = True.
Proof. exact (TRANS (@lem8003914 _141853 _141854 _141855 s t P) (@lem8003918 _141853 _141854 _141855 s t P)). Qed.
Lemma lem8003920 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : True = ((term19 _141853 _141854 _141855 s t P) = (term63 _141853 _141854 _141855 s t P)).
Proof. exact (SYM (@lem8003919 _141853 _141854 _141855 s t P)). Qed.
