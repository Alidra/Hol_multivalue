Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_DISJOINT_UNION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_INTER_spec.
Require Import PAIR_EQ_spec.
Require Import disjoint_union_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm69_spec.
Lemma lem4475750 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4475751 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4475752 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4475751 t1) (@lem4475750 t1)). Qed.
Lemma lem4475753 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4475752 t1 t2). Qed.
Lemma lem4475754 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4475755 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4475754 t1 t2) (@lem4475753 t1 t2)). Qed.
Lemma lem4475756 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4475755 t1 t2 t3). Qed.
Lemma lem4475757 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4475758 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4475757 t1 t2 t3) (@lem4475756 t1 t2 t3)). Qed.
Lemma lem4475759 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4475758 t1 t2 t3)). Qed.
Lemma lem4475791 {_83064 : Type'} : term7 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4475792 {_83064 : Type'} (P : type919 _83064) : term8 _83064 P.
Proof. exact (@lem4475791 _83064 P). Qed.
Lemma lem4475793 {_83064 : Type'} (P : type919 _83064) : (term8 _83064 P) = (term9 _83064 P).
Proof. exact (eq_refl (term8 _83064 P)). Qed.
Lemma lem4475794 {_83064 : Type'} (P : type919 _83064) : term9 _83064 P.
Proof. exact (EQ_MP (@lem4475793 _83064 P) (@lem4475792 _83064 P)). Qed.
Lemma lem4475795 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term10 _83064 P x.
Proof. exact (@lem4475794 _83064 P x). Qed.
Lemma lem4475796 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term10 _83064 P x) = ((term11 _83064 x P) = (term12 _83064 P x)).
Proof. exact (eq_refl (term10 _83064 P x)). Qed.
Lemma lem4475798 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4475799 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem4475800 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem4475799 A s) (@lem4475798 A s)). Qed.
Lemma lem4475801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem4475800 A s t). Qed.
Lemma lem4475802 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term16 A s t).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem4475803 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (EQ_MP (@lem4475802 A s t) (@lem4475801 A s t)). Qed.
Lemma lem4475804 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term17 A s t x.
Proof. exact (@lem4475803 A s t x). Qed.
Lemma lem4475805 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term17 A s t x) = ((term18 A x s t) = (term19 A s x t)).
Proof. exact (eq_refl (term17 A s t x)). Qed.
Lemma lem4475807 {A K : Type'} (k : K -> Prop) : term20 A K k.
Proof. exact (@lem4464464 A K k). Qed.
Lemma lem4475808 {A K : Type'} (k : K -> Prop) : (term20 A K k) = (term21 A K k).
Proof. exact (eq_refl (term20 A K k)). Qed.
Lemma lem4475809 {A K : Type'} (k : K -> Prop) : term21 A K k.
Proof. exact (EQ_MP (@lem4475808 A K k) (@lem4475807 A K k)). Qed.
Lemma lem4475810 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term22 A K k s.
Proof. exact (@lem4475809 A K k s). Qed.
Lemma lem4475811 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = ((@disjoint_union A K k s) = (term23 A K k s)).
Proof. exact (eq_refl (term22 A K k s)). Qed.
Lemma lem4475813 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4475814 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4475815 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem4475814 A s) (@lem4475813 A s)). Qed.
Lemma lem4475816 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem4475815 A s t). Qed.
Lemma lem4475817 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem4475822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4475817 A s t) (@lem4475816 A s t)). Qed.
Lemma lem4475823 {A K : Type'} (s : type1223 A K) (t : type1223 A K) : (s = t) = (term28 A K s t).
Proof. exact (@lem4475822 (prod K A) s t). Qed.
Lemma lem4475824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term29 A K s k t) = (term30 A K k s t)) = (term31 A K k s t).
Proof. exact (@lem4475823 A K (term29 A K s k t) (term30 A K k s t)). Qed.
Lemma lem4475834 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (EQ_MP (@lem4475805 A s x t) (@lem4475804 A s t x)). Qed.
Lemma lem4475835 {A K : Type'} (s : type1223 A K) (x : prod K A) (t : type1223 A K) : (term32 A K x s t) = (term33 A K s x t).
Proof. exact (@lem4475834 (prod K A) s x t). Qed.
Lemma lem4475836 {A K : Type'} (s : type1470 A K) (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term34 A K x s k t) = (term35 A K s x k t).
Proof. exact (@lem4475835 A K (@disjoint_union A K k s) x (@disjoint_union A K k t)). Qed.
Lemma lem4475840 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4475811 A K k s) (@lem4475810 A K k s)). Qed.
Lemma lem4475841 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4475840 A K k s). Qed.
Lemma lem4475852 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4475853 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term36 A K x k s) = (term37 A K x k s).
Proof. exact (MK_COMB (@lem4475852 A K x) (@lem4475841 A K k s)). Qed.
Lemma lem4475855 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4475796 _83064 P x) (@lem4475795 _83064 P x)). Qed.
Lemma lem4475856 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4475855 (prod K A) P x). Qed.
Lemma lem4475857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term40 A K x k s) = (term41 A K k s x).
Proof. exact (@lem4475856 A K (term42 A K k s) x). Qed.
Lemma lem4475858 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) : (term43 A K k s GEN_PVAR_143) = (term44 A K GEN_PVAR_143 k s).
Proof. exact (eq_refl (term43 A K k s GEN_PVAR_143)). Qed.
Lemma lem4475859 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term45 A K k s) = (term46 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4475858 A K GEN_PVAR_143 k s)). Qed.
Lemma lem4475860 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4475861 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term47 A K k s) = (term23 A K k s).
Proof. exact (MK_COMB (@lem4475860 A K) (@lem4475859 A K k s)). Qed.
Lemma lem4475862 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4475863 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term40 A K x k s) = (term37 A K x k s).
Proof. exact (MK_COMB (@lem4475862 A K x) (@lem4475861 A K k s)). Qed.
Lemma lem4475864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475865 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term48 A K x k s) = (term49 A K x k s).
Proof. exact (MK_COMB (@lem4475864) (@lem4475863 A K x k s)). Qed.
Lemma lem4475866 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term41 A K k s x) = (term50 A K x k s).
Proof. exact (eq_refl (term41 A K k s x)). Qed.
Lemma lem4475867 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : ((term40 A K x k s) = (term41 A K k s x)) = ((term37 A K x k s) = (term50 A K x k s)).
Proof. exact (MK_COMB (@lem4475865 A K x k s) (@lem4475866 A K x k s)). Qed.
Lemma lem4475868 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) : (term37 A K x k s) = (term50 A K x k s).
Proof. exact (EQ_MP (@lem4475867 A K x k s) (@lem4475857 A K k s x)). Qed.
Lemma lem4475878 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4475879 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4475878 Prop (type1223 A K) f y). Qed.
Lemma lem4475880 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term53 A K x k x' s i) = (term54 A K x k x' s i).
Proof. exact (@lem4475879 A K (term55 A K x) (term56 A K k x' s i)). Qed.
Lemma lem4475881 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4475882 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4475881 A K p x)). Qed.
Lemma lem4475883 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term56 A K k x s i) = (term56 A K k x s i).
Proof. exact (eq_refl (term56 A K k x s i)). Qed.
Lemma lem4475884 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term53 A K x k x' s i) = (term54 A K x k x' s i).
Proof. exact (MK_COMB (@lem4475882 A K x) (@lem4475883 A K k x' s i)). Qed.
Lemma lem4475885 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4475886 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (s : type1470 A K) (i : K) : (term60 A K x k x' s i) = (term61 A K x k x' s i).
Proof. exact (MK_COMB (@lem4475885 A K) (@lem4475884 A K x k x' s i)). Qed.
Lemma lem4475887 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x s i) = (term62 A K k x s i x').
Proof. exact (eq_refl (term54 A K x' k x s i)). Qed.
Lemma lem4475888 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : ((term53 A K x' k x s i) = (term54 A K x' k x s i)) = ((term54 A K x' k x s i) = (term62 A K k x s i x')).
Proof. exact (MK_COMB (@lem4475886 A K x' k x s i) (@lem4475887 A K k x s i x')). Qed.
Lemma lem4475889 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x s i) = (term62 A K k x s i x').
Proof. exact (EQ_MP (@lem4475888 A K k x s i x') (@lem4475880 A K x' k x s i)). Qed.
Lemma lem4475898 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4475899 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k s i x') = (term64 A K k s x i x').
Proof. exact (MK_COMB (@lem4475889 A K k x' s i x) (@lem4475898 A K i x')). Qed.
Lemma lem4475901 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4475902 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4475901 (prod K A) Prop f y). Qed.
Lemma lem4475903 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k s x i x') = (term64 A K k s x i x').
Proof. exact (@lem4475902 A K (term62 A K k x' s i x) (@pair K A i x')). Qed.
Lemma lem4475904 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) (t : prod K A) : (term67 A K k x s i x' t) = (term68 A K k x s i x' t).
Proof. exact (eq_refl (term67 A K k x s i x' t)). Qed.
Lemma lem4475905 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (x' : prod K A) : (term69 A K k x s i x') = (term62 A K k x s i x').
Proof. exact (fun_ext (fun t : prod K A => @lem4475904 A K k x s i x' t)). Qed.
Lemma lem4475906 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4475907 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k s x i x') = (term64 A K k s x i x').
Proof. exact (MK_COMB (@lem4475905 A K k x' s i x) (@lem4475906 A K i x')). Qed.
Lemma lem4475908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475909 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term70 A K k s x i x') = (term71 A K k s x i x').
Proof. exact (MK_COMB (@lem4475908) (@lem4475907 A K k s x i x')). Qed.
Lemma lem4475910 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term64 A K k s x i x')). Qed.
Lemma lem4475911 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term66 A K k s x i x') = (term64 A K k s x i x')) = ((term64 A K k s x i x') = (term72 A K k s x i x')).
Proof. exact (MK_COMB (@lem4475909 A K k s x i x') (@lem4475910 A K k s x i x')). Qed.
Lemma lem4475912 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (EQ_MP (@lem4475911 A K k s x i x') (@lem4475903 A K k s x i x')). Qed.
Lemma lem4475921 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k s i x') = (term72 A K k s x i x').
Proof. exact (TRANS (@lem4475899 A K k s x i x') (@lem4475912 A K k s x i x')). Qed.
Lemma lem4475922 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term73 A K x k s i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4475921 A K k s x i x')). Qed.
Lemma lem4475923 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4475924 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term75 A K x k s i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4475923 A) (@lem4475922 A K k s x i)). Qed.
Lemma lem4475929 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term77 A K x k s) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4475924 A K k s x i)). Qed.
Lemma lem4475930 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4475931 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term50 A K x k s) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4475930 K) (@lem4475929 A K k s x)). Qed.
Lemma lem4475936 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term37 A K x k s) = (term79 A K k s x).
Proof. exact (TRANS (@lem4475868 A K x k s) (@lem4475931 A K k s x)). Qed.
Lemma lem4475937 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term36 A K x k s) = (term79 A K k s x).
Proof. exact (TRANS (@lem4475853 A K x k s) (@lem4475936 A K k s x)). Qed.
Lemma lem4475938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4475939 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term80 A K x k s) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4475938) (@lem4475937 A K k s x)). Qed.
Lemma lem4475941 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4475811 A K k s) (@lem4475810 A K k s)). Qed.
Lemma lem4475942 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4475941 A K k s). Qed.
Lemma lem4475943 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@disjoint_union A K k t) = (term23 A K k t).
Proof. exact (@lem4475942 A K k t). Qed.
Lemma lem4475954 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4475955 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term36 A K x k t) = (term37 A K x k t).
Proof. exact (MK_COMB (@lem4475954 A K x) (@lem4475943 A K k t)). Qed.
Lemma lem4475957 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4475796 _83064 P x) (@lem4475795 _83064 P x)). Qed.
Lemma lem4475958 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4475957 (prod K A) P x). Qed.
Lemma lem4475959 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term40 A K x k t) = (term41 A K k t x).
Proof. exact (@lem4475958 A K (term42 A K k t) x). Qed.
Lemma lem4475960 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (t : type1470 A K) : (term43 A K k t GEN_PVAR_143) = (term44 A K GEN_PVAR_143 k t).
Proof. exact (eq_refl (term43 A K k t GEN_PVAR_143)). Qed.
Lemma lem4475961 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term45 A K k t) = (term46 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4475960 A K GEN_PVAR_143 k t)). Qed.
Lemma lem4475962 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4475963 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term47 A K k t) = (term23 A K k t).
Proof. exact (MK_COMB (@lem4475962 A K) (@lem4475961 A K k t)). Qed.
Lemma lem4475964 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4475965 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term40 A K x k t) = (term37 A K x k t).
Proof. exact (MK_COMB (@lem4475964 A K x) (@lem4475963 A K k t)). Qed.
Lemma lem4475966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4475967 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term48 A K x k t) = (term49 A K x k t).
Proof. exact (MK_COMB (@lem4475966) (@lem4475965 A K x k t)). Qed.
Lemma lem4475968 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term41 A K k t x) = (term50 A K x k t).
Proof. exact (eq_refl (term41 A K k t x)). Qed.
Lemma lem4475969 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : ((term40 A K x k t) = (term41 A K k t x)) = ((term37 A K x k t) = (term50 A K x k t)).
Proof. exact (MK_COMB (@lem4475967 A K x k t) (@lem4475968 A K x k t)). Qed.
Lemma lem4475970 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) : (term37 A K x k t) = (term50 A K x k t).
Proof. exact (EQ_MP (@lem4475969 A K x k t) (@lem4475959 A K k t x)). Qed.
Lemma lem4475980 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4475981 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4475980 Prop (type1223 A K) f y). Qed.
Lemma lem4475982 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term53 A K x k x' t i) = (term54 A K x k x' t i).
Proof. exact (@lem4475981 A K (term55 A K x) (term56 A K k x' t i)). Qed.
Lemma lem4475983 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4475984 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4475983 A K p x)). Qed.
Lemma lem4475985 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term56 A K k x t i) = (term56 A K k x t i).
Proof. exact (eq_refl (term56 A K k x t i)). Qed.
Lemma lem4475986 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term53 A K x k x' t i) = (term54 A K x k x' t i).
Proof. exact (MK_COMB (@lem4475984 A K x) (@lem4475985 A K k x' t i)). Qed.
Lemma lem4475987 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4475988 {A K : Type'} (x : prod K A) (k : K -> Prop) (x' : A) (t : type1470 A K) (i : K) : (term60 A K x k x' t i) = (term61 A K x k x' t i).
Proof. exact (MK_COMB (@lem4475987 A K) (@lem4475986 A K x k x' t i)). Qed.
Lemma lem4475989 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x t i) = (term62 A K k x t i x').
Proof. exact (eq_refl (term54 A K x' k x t i)). Qed.
Lemma lem4475990 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : ((term53 A K x' k x t i) = (term54 A K x' k x t i)) = ((term54 A K x' k x t i) = (term62 A K k x t i x')).
Proof. exact (MK_COMB (@lem4475988 A K x' k x t i) (@lem4475989 A K k x t i x')). Qed.
Lemma lem4475991 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term54 A K x' k x t i) = (term62 A K k x t i x').
Proof. exact (EQ_MP (@lem4475990 A K k x t i x') (@lem4475982 A K x' k x t i)). Qed.
Lemma lem4476000 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4476001 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k t i x') = (term64 A K k t x i x').
Proof. exact (MK_COMB (@lem4475991 A K k x' t i x) (@lem4476000 A K i x')). Qed.
Lemma lem4476003 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4476004 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4476003 (prod K A) Prop f y). Qed.
Lemma lem4476005 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k t x i x') = (term64 A K k t x i x').
Proof. exact (@lem4476004 A K (term62 A K k x' t i x) (@pair K A i x')). Qed.
Lemma lem4476006 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) (t' : prod K A) : (term67 A K k x t i x' t') = (term68 A K k x t i x' t').
Proof. exact (eq_refl (term67 A K k x t i x' t')). Qed.
Lemma lem4476007 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term69 A K k x t i x') = (term62 A K k x t i x').
Proof. exact (fun_ext (fun t' : prod K A => @lem4476006 A K k x t i x' t')). Qed.
Lemma lem4476008 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4476009 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term66 A K k t x i x') = (term64 A K k t x i x').
Proof. exact (MK_COMB (@lem4476007 A K k x' t i x) (@lem4476008 A K i x')). Qed.
Lemma lem4476010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4476011 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term70 A K k t x i x') = (term71 A K k t x i x').
Proof. exact (MK_COMB (@lem4476010) (@lem4476009 A K k t x i x')). Qed.
Lemma lem4476012 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term64 A K k t x i x')). Qed.
Lemma lem4476013 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term66 A K k t x i x') = (term64 A K k t x i x')) = ((term64 A K k t x i x') = (term72 A K k t x i x')).
Proof. exact (MK_COMB (@lem4476011 A K k t x i x') (@lem4476012 A K k t x i x')). Qed.
Lemma lem4476014 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term64 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (EQ_MP (@lem4476013 A K k t x i x') (@lem4476005 A K k t x i x')). Qed.
Lemma lem4476023 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term63 A K x k t i x') = (term72 A K k t x i x').
Proof. exact (TRANS (@lem4476001 A K k t x i x') (@lem4476014 A K k t x i x')). Qed.
Lemma lem4476024 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term73 A K x k t i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476023 A K k t x i x')). Qed.
Lemma lem4476025 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476026 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term75 A K x k t i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4476025 A) (@lem4476024 A K k t x i)). Qed.
Lemma lem4476031 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term77 A K x k t) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4476026 A K k t x i)). Qed.
Lemma lem4476032 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476033 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term50 A K x k t) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4476032 K) (@lem4476031 A K k t x)). Qed.
Lemma lem4476038 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term37 A K x k t) = (term79 A K k t x).
Proof. exact (TRANS (@lem4475970 A K x k t) (@lem4476033 A K k t x)). Qed.
Lemma lem4476039 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term36 A K x k t) = (term79 A K k t x).
Proof. exact (TRANS (@lem4475955 A K x k t) (@lem4476038 A K k t x)). Qed.
Lemma lem4476040 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term35 A K s x k t) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4475939 A K k s x) (@lem4476039 A K k t x)). Qed.
Lemma lem4476043 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term34 A K x s k t) = (term82 A K s k t x).
Proof. exact (TRANS (@lem4475836 A K s x k t) (@lem4476040 A K s k t x)). Qed.
Lemma lem4476044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4476045 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term83 A K x s k t) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4476044) (@lem4476043 A K s k t x)). Qed.
Lemma lem4476047 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (EQ_MP (@lem4475811 A K k s) (@lem4475810 A K k s)). Qed.
Lemma lem4476048 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@disjoint_union A K k s) = (term23 A K k s).
Proof. exact (@lem4476047 A K k s). Qed.
Lemma lem4476049 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term30 A K k s t) = (term85 A K k s t).
Proof. exact (@lem4476048 A K k (term86 A K s t)). Qed.
Lemma lem4476061 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4476062 {A K : Type'} (f : type1470 A K) (y : K) : (term87 A K f y) = (f y).
Proof. exact (@lem4476061 K (A -> Prop) f y). Qed.
Lemma lem4476063 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term88 A K s t i) = (term89 A K s t i).
Proof. exact (@lem4476062 A K (term86 A K s t) i). Qed.
Lemma lem4476064 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (eq_refl (term89 A K s t i)). Qed.
Lemma lem4476065 {A K : Type'} (s : type1470 A K) (t : type1470 A K) : (term91 A K s t) = (term86 A K s t).
Proof. exact (fun_ext (fun i : K => @lem4476064 A K s t i)). Qed.
Lemma lem4476066 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4476067 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term88 A K s t i) = (term89 A K s t i).
Proof. exact (MK_COMB (@lem4476065 A K s t) (@lem4476066 K i)). Qed.
Lemma lem4476068 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4476069 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term92 A K s t i) = (term93 A K s t i).
Proof. exact (MK_COMB (@lem4476068 A) (@lem4476067 A K s t i)). Qed.
Lemma lem4476070 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (eq_refl (term89 A K s t i)). Qed.
Lemma lem4476071 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term88 A K s t i) = (term89 A K s t i)) = ((term89 A K s t i) = (term90 A K s t i)).
Proof. exact (MK_COMB (@lem4476069 A K s t i) (@lem4476070 A K s t i)). Qed.
Lemma lem4476072 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term89 A K s t i) = (term90 A K s t i).
Proof. exact (EQ_MP (@lem4476071 A K s t i) (@lem4476063 A K s t i)). Qed.
Lemma lem4476073 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4476074 {A K : Type'} (x : A) (s : type1470 A K) (t : type1470 A K) (i : K) : (term94 A K x s t i) = (term95 A K x s t i).
Proof. exact (MK_COMB (@lem4476073 A x) (@lem4476072 A K s t i)). Qed.
Lemma lem4476076 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (EQ_MP (@lem4475805 A s x t) (@lem4475804 A s t x)). Qed.
Lemma lem4476077 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term18 A x s t) = (term19 A s x t).
Proof. exact (@lem4476076 A s x t). Qed.
Lemma lem4476078 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term95 A K x s t i) = (term96 A K s x t i).
Proof. exact (@lem4476077 A (s i) x (t i)). Qed.
Lemma lem4476081 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term94 A K x s t i) = (term96 A K s x t i).
Proof. exact (TRANS (@lem4476074 A K x s t i) (@lem4476078 A K s x t i)). Qed.
Lemma lem4476082 {K : Type'} (i : K) (k : K -> Prop) : (term97 K i k) = (term97 K i k).
Proof. exact (eq_refl (term97 K i k)). Qed.
Lemma lem4476083 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term98 A K k x s t i) = (term99 A K k s x t i).
Proof. exact (MK_COMB (@lem4476082 K i k) (@lem4476081 A K s x t i)). Qed.
Lemma lem4476086 {A K : Type'} (GEN_PVAR_143 : prod K A) : (@SETSPEC (prod K A) GEN_PVAR_143) = (@SETSPEC (prod K A) GEN_PVAR_143).
Proof. exact (eq_refl (@SETSPEC (prod K A) GEN_PVAR_143)). Qed.
Lemma lem4476087 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term100 A K GEN_PVAR_143 k x s t i) = (term101 A K GEN_PVAR_143 k s x t i).
Proof. exact (MK_COMB (@lem4476086 A K GEN_PVAR_143) (@lem4476083 A K k s x t i)). Qed.
Lemma lem4476088 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4476089 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term102 A K GEN_PVAR_143 k s t i x) = (term103 A K GEN_PVAR_143 k s t i x).
Proof. exact (MK_COMB (@lem4476087 A K GEN_PVAR_143 k s x t i) (@lem4476088 A K i x)). Qed.
Lemma lem4476090 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term104 A K GEN_PVAR_143 k s t i) = (term105 A K GEN_PVAR_143 k s t i).
Proof. exact (fun_ext (fun x : A => @lem4476089 A K GEN_PVAR_143 k s t i x)). Qed.
Lemma lem4476091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476092 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term106 A K GEN_PVAR_143 k s t i) = (term107 A K GEN_PVAR_143 k s t i).
Proof. exact (MK_COMB (@lem4476091 A) (@lem4476090 A K GEN_PVAR_143 k s t i)). Qed.
Lemma lem4476097 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term108 A K GEN_PVAR_143 k s t) = (term109 A K GEN_PVAR_143 k s t).
Proof. exact (fun_ext (fun i : K => @lem4476092 A K GEN_PVAR_143 k s t i)). Qed.
Lemma lem4476098 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476099 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term110 A K GEN_PVAR_143 k s t) = (term111 A K GEN_PVAR_143 k s t).
Proof. exact (MK_COMB (@lem4476098 K) (@lem4476097 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4476104 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term112 A K k s t) = (term113 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4476099 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4476105 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4476106 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term85 A K k s t) = (term114 A K k s t).
Proof. exact (MK_COMB (@lem4476105 A K) (@lem4476104 A K k s t)). Qed.
Lemma lem4476107 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term30 A K k s t) = (term114 A K k s t).
Proof. exact (TRANS (@lem4476049 A K k s t) (@lem4476106 A K k s t)). Qed.
Lemma lem4476108 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4476109 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term115 A K x k s t) = (term116 A K x k s t).
Proof. exact (MK_COMB (@lem4476108 A K x) (@lem4476107 A K k s t)). Qed.
Lemma lem4476111 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term11 _83064 x P) = (term12 _83064 P x).
Proof. exact (EQ_MP (@lem4475796 _83064 P x) (@lem4475795 _83064 P x)). Qed.
Lemma lem4476112 {A K : Type'} (P : type916 A K) (x : prod K A) : (term38 A K x P) = (term39 A K P x).
Proof. exact (@lem4476111 (prod K A) P x). Qed.
Lemma lem4476113 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term117 A K x k s t) = (term118 A K k s t x).
Proof. exact (@lem4476112 A K (term119 A K k s t) x). Qed.
Lemma lem4476114 {A K : Type'} (GEN_PVAR_143 : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term120 A K k s t GEN_PVAR_143) = (term111 A K GEN_PVAR_143 k s t).
Proof. exact (eq_refl (term120 A K k s t GEN_PVAR_143)). Qed.
Lemma lem4476115 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term121 A K k s t) = (term113 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_143 : prod K A => @lem4476114 A K GEN_PVAR_143 k s t)). Qed.
Lemma lem4476116 {A K : Type'} : (@GSPEC (prod K A)) = (@GSPEC (prod K A)).
Proof. exact (eq_refl (@GSPEC (prod K A))). Qed.
Lemma lem4476117 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term122 A K k s t) = (term114 A K k s t).
Proof. exact (MK_COMB (@lem4476116 A K) (@lem4476115 A K k s t)). Qed.
Lemma lem4476118 {A K : Type'} (x : prod K A) : (@IN (prod K A) x) = (@IN (prod K A) x).
Proof. exact (eq_refl (@IN (prod K A) x)). Qed.
Lemma lem4476119 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term117 A K x k s t) = (term116 A K x k s t).
Proof. exact (MK_COMB (@lem4476118 A K x) (@lem4476117 A K k s t)). Qed.
Lemma lem4476120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4476121 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term123 A K x k s t) = (term124 A K x k s t).
Proof. exact (MK_COMB (@lem4476120) (@lem4476119 A K x k s t)). Qed.
Lemma lem4476122 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term118 A K k s t x) = (term125 A K x k s t).
Proof. exact (eq_refl (term118 A K k s t x)). Qed.
Lemma lem4476123 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term117 A K x k s t) = (term118 A K k s t x)) = ((term116 A K x k s t) = (term125 A K x k s t)).
Proof. exact (MK_COMB (@lem4476121 A K x k s t) (@lem4476122 A K x k s t)). Qed.
Lemma lem4476124 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term116 A K x k s t) = (term125 A K x k s t).
Proof. exact (EQ_MP (@lem4476123 A K x k s t) (@lem4476113 A K k s t x)). Qed.
Lemma lem4476134 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4476135 {A K : Type'} (f : type1534 A K) (y : Prop) : (term52 A K f y) = (f y).
Proof. exact (@lem4476134 Prop (type1223 A K) f y). Qed.
Lemma lem4476136 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term126 A K x k s x' t i) = (term127 A K x k s x' t i).
Proof. exact (@lem4476135 A K (term55 A K x) (term99 A K k s x' t i)). Qed.
Lemma lem4476137 {A K : Type'} (p : Prop) (x : prod K A) : (term57 A K x p) = (term58 A K p x).
Proof. exact (eq_refl (term57 A K x p)). Qed.
Lemma lem4476138 {A K : Type'} (x : prod K A) : (term59 A K x) = (term55 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4476137 A K p x)). Qed.
Lemma lem4476139 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term99 A K k s x t i) = (term99 A K k s x t i).
Proof. exact (eq_refl (term99 A K k s x t i)). Qed.
Lemma lem4476140 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term126 A K x k s x' t i) = (term127 A K x k s x' t i).
Proof. exact (MK_COMB (@lem4476138 A K x) (@lem4476139 A K k s x' t i)). Qed.
Lemma lem4476141 {A K : Type'} : (@eq ((prod K A) -> Prop)) = (@eq ((prod K A) -> Prop)).
Proof. exact (eq_refl (@eq ((prod K A) -> Prop))). Qed.
Lemma lem4476142 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (x' : A) (t : type1470 A K) (i : K) : (term128 A K x k s x' t i) = (term129 A K x k s x' t i).
Proof. exact (MK_COMB (@lem4476141 A K) (@lem4476140 A K x k s x' t i)). Qed.
Lemma lem4476143 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term127 A K x' k s x t i) = (term130 A K k s x t i x').
Proof. exact (eq_refl (term127 A K x' k s x t i)). Qed.
Lemma lem4476144 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : ((term126 A K x' k s x t i) = (term127 A K x' k s x t i)) = ((term127 A K x' k s x t i) = (term130 A K k s x t i x')).
Proof. exact (MK_COMB (@lem4476142 A K x' k s x t i) (@lem4476143 A K k s x t i x')). Qed.
Lemma lem4476145 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term127 A K x' k s x t i) = (term130 A K k s x t i x').
Proof. exact (EQ_MP (@lem4476144 A K k s x t i x') (@lem4476136 A K x' k s x t i)). Qed.
Lemma lem4476156 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4476157 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term131 A K x k s t i x') = (term132 A K k s t x i x').
Proof. exact (MK_COMB (@lem4476145 A K k s x' t i x) (@lem4476156 A K i x')). Qed.
Lemma lem4476159 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4476160 {A K : Type'} (f : type1223 A K) (y : prod K A) : (term65 A K f y) = (f y).
Proof. exact (@lem4476159 (prod K A) Prop f y). Qed.
Lemma lem4476161 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term133 A K k s t x i x') = (term132 A K k s t x i x').
Proof. exact (@lem4476160 A K (term130 A K k s x' t i x) (@pair K A i x')). Qed.
Lemma lem4476162 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) (t' : prod K A) : (term134 A K k s x t i x' t') = (term135 A K k s x t i x' t').
Proof. exact (eq_refl (term134 A K k s x t i x' t')). Qed.
Lemma lem4476163 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) (x' : prod K A) : (term136 A K k s x t i x') = (term130 A K k s x t i x').
Proof. exact (fun_ext (fun t' : prod K A => @lem4476162 A K k s x t i x' t')). Qed.
Lemma lem4476164 {A K : Type'} (i : K) (x : A) : (@pair K A i x) = (@pair K A i x).
Proof. exact (eq_refl (@pair K A i x)). Qed.
Lemma lem4476165 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term133 A K k s t x i x') = (term132 A K k s t x i x').
Proof. exact (MK_COMB (@lem4476163 A K k s x' t i x) (@lem4476164 A K i x')). Qed.
Lemma lem4476166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4476167 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term137 A K k s t x i x') = (term138 A K k s t x i x').
Proof. exact (MK_COMB (@lem4476166) (@lem4476165 A K k s t x i x')). Qed.
Lemma lem4476168 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term132 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term132 A K k s t x i x')). Qed.
Lemma lem4476169 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term133 A K k s t x i x') = (term132 A K k s t x i x')) = ((term132 A K k s t x i x') = (term139 A K k s t x i x')).
Proof. exact (MK_COMB (@lem4476167 A K k s t x i x') (@lem4476168 A K k s t x i x')). Qed.
Lemma lem4476170 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term132 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (EQ_MP (@lem4476169 A K k s t x i x') (@lem4476161 A K k s t x i x')). Qed.
Lemma lem4476181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term131 A K x k s t i x') = (term139 A K k s t x i x').
Proof. exact (TRANS (@lem4476157 A K k s t x i x') (@lem4476170 A K k s t x i x')). Qed.
Lemma lem4476182 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term140 A K x k s t i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476181 A K k s t x i x')). Qed.
Lemma lem4476183 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term142 A K x k s t i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4476183 A) (@lem4476182 A K k s t x i)). Qed.
Lemma lem4476189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term144 A K x k s t) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4476184 A K k s t x i)). Qed.
Lemma lem4476190 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476191 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term125 A K x k s t) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4476190 K) (@lem4476189 A K k s t x)). Qed.
Lemma lem4476196 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term116 A K x k s t) = (term146 A K k s t x).
Proof. exact (TRANS (@lem4476124 A K x k s t) (@lem4476191 A K k s t x)). Qed.
Lemma lem4476197 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term115 A K x k s t) = (term146 A K k s t x).
Proof. exact (TRANS (@lem4476109 A K x k s t) (@lem4476196 A K k s t x)). Qed.
Lemma lem4476198 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term34 A K x s k t) = (term115 A K x k s t)) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (MK_COMB (@lem4476045 A K s k t x) (@lem4476197 A K k s t x)). Qed.
Lemma lem4476203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term147 A K k s t) = (term148 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4476198 A K k s t x)). Qed.
Lemma lem4476204 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476205 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term31 A K k s t) = (term149 A K k s t).
Proof. exact (MK_COMB (@lem4476204 A K) (@lem4476203 A K k s t)). Qed.
Lemma lem4476210 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term29 A K s k t) = (term30 A K k s t)) = (term149 A K k s t).
Proof. exact (TRANS (@lem4475824 A K k s t) (@lem4476205 A K k s t)). Qed.
Lemma lem4476211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = ((term29 A K s k t) = (term30 A K k s t)).
Proof. exact (SYM (@lem4476210 A K k s t)). Qed.
Lemma lem4476213 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4476214 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = (term151 A K k s t).
Proof. exact (@lem4476213 (term149 A K k s t)). Qed.
Lemma lem4476215 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term151 A K k s t) = (term149 A K k s t).
Proof. exact (SYM (@lem4476214 A K k s t)). Qed.
Lemma lem4476216 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term152 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4476217 {A K : Type'} : term153 A K.
Proof. exact (@lem47438 K A). Qed.
Lemma lem4476219 {A B K : Type'} : term154 A B K.
Proof. exact (@lem47438 (prod K A) B). Qed.
Lemma lem4476220 {A K : Type'} : term155 A K.
Proof. exact (@lem47438 A (prod K A)). Qed.
Lemma lem4476223 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term156 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4476224 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (fun h0 : term156 A B K k s t => @lem4476223 A B K k s t h0). Qed.
Lemma lem4476225 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4476226 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term156 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4476227 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) (h2 : term157 A B K k s t) : term156 A B K k s t.
Proof. exact (@lem4476225 A B K k s t h2 (@lem4476226 A B K k s t h1)). Qed.
Lemma lem4476228 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) : term158 A B K k s t.
Proof. exact (fun h0 : term157 A B K k s t => @lem4476227 A B K k s t h1 h0). Qed.
Lemma lem4476229 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (h1). Qed.
Lemma lem4476230 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term156 A B K k s t) (h2 : term157 A B K k s t) : term156 A B K k s t.
Proof. exact (@lem4476228 A B K k s t h1 (@lem4476229 A B K k s t h2)). Qed.
Lemma lem4476231 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term157 A B K k s t) : term157 A B K k s t.
Proof. exact (fun h0 : term156 A B K k s t => @lem4476230 A B K k s t h0 h1). Qed.
Lemma lem4476232 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term159 A B K k s t.
Proof. exact (fun h0 : term157 A B K k s t => @lem4476231 A B K k s t h0). Qed.
Lemma lem4476235 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (@lem4476232 A B K k s t (@lem4476224 A B K k s t)). Qed.
Lemma lem4476236 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term157 A B K k s t.
Proof. exact (@lem4476235 A B K k s t). Qed.
Lemma lem4476468 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4476469 {A B K : Type'} : (term160 A B K) = (term161 A B K).
Proof. exact (@lem4476468 (term154 A B K)). Qed.
Lemma lem4476488 {A K : Type'} : (term162 A K) = (term162 A K).
Proof. exact (eq_refl (term162 A K)). Qed.
Lemma lem4476489 {A B K : Type'} : (term163 A B K) = (term164 A B K).
Proof. exact (MK_COMB (@lem4476488 A K) (@lem4476469 A B K)). Qed.
Lemma lem4476492 {A K : Type'} : (term165 A K) = (term165 A K).
Proof. exact (eq_refl (term165 A K)). Qed.
Lemma lem4476493 {A B K : Type'} : (term166 A B K) = (term167 A B K).
Proof. exact (MK_COMB (@lem4476492 A K) (@lem4476489 A B K)). Qed.
Lemma lem4476496 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term168 A K k s t) = (term168 A K k s t).
Proof. exact (eq_refl (term168 A K k s t)). Qed.
Lemma lem4476497 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term156 A B K k s t) = (term169 A B K k s t).
Proof. exact (MK_COMB (@lem4476496 A K k s t) (@lem4476493 A B K)). Qed.
Lemma lem4476500 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term170 A B K s t) = (term171 A B K s t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4476497 A B K k s t)). Qed.
Lemma lem4476501 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4476502 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term172 A B K s t) = (term173 A B K s t).
Proof. exact (MK_COMB (@lem4476501 K) (@lem4476500 A B K s t)). Qed.
Lemma lem4476507 {A B K : Type'} (t : type1470 A K) : (term174 A B K t) = (term175 A B K t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4476502 A B K s t)). Qed.
Lemma lem4476508 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4476509 {A B K : Type'} (t : type1470 A K) : (term176 A B K t) = (term177 A B K t).
Proof. exact (MK_COMB (@lem4476508 A K) (@lem4476507 A B K t)). Qed.
Lemma lem4476514 {A B K : Type'} : (term178 A B K) = (term179 A B K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4476509 A B K t)). Qed.
Lemma lem4476515 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4476524 {A B K : Type'} : (term180 A B K) = (term181 A B K).
Proof. exact (MK_COMB (@lem4476515 A K) (@lem4476514 A B K)). Qed.
Lemma lem4476533 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) (b : B) : (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b)) = (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b)).
Proof. exact (eq_refl (((@pair (prod K A) B x y) = (@pair (prod K A) B a b)) = (term182 A B K x a y b))). Qed.
Lemma lem4476534 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) : (term183 A B K x a y) = (term183 A B K x a y).
Proof. exact (fun_ext (fun b : B => @lem4476533 A B K x a y b)). Qed.
Lemma lem4476535 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4476536 {A B K : Type'} (x : prod K A) (a : prod K A) (y : B) : (term184 A B K x a y) = (term184 A B K x a y).
Proof. exact (MK_COMB (@lem4476535 B) (@lem4476534 A B K x a y)). Qed.
Lemma lem4476537 {A B K : Type'} (x : prod K A) (y : B) : (term185 A B K x y) = (term185 A B K x y).
Proof. exact (fun_ext (fun a : prod K A => @lem4476536 A B K x a y)). Qed.
Lemma lem4476538 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476539 {A B K : Type'} (x : prod K A) (y : B) : (term186 A B K x y) = (term186 A B K x y).
Proof. exact (MK_COMB (@lem4476538 A K) (@lem4476537 A B K x y)). Qed.
Lemma lem4476540 {A B K : Type'} (x : prod K A) : (term187 A B K x) = (term187 A B K x).
Proof. exact (fun_ext (fun y : B => @lem4476539 A B K x y)). Qed.
Lemma lem4476541 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4476542 {A B K : Type'} (x : prod K A) : (term188 A B K x) = (term188 A B K x).
Proof. exact (MK_COMB (@lem4476541 B) (@lem4476540 A B K x)). Qed.
Lemma lem4476543 {A B K : Type'} : (term189 A B K) = (term189 A B K).
Proof. exact (fun_ext (fun x : prod K A => @lem4476542 A B K x)). Qed.
Lemma lem4476544 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476545 {A B K : Type'} : (term154 A B K) = (term154 A B K).
Proof. exact (MK_COMB (@lem4476544 A K) (@lem4476543 A B K)). Qed.
Lemma lem4476546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476547 {A B K : Type'} : (term161 A B K) = (term161 A B K).
Proof. exact (MK_COMB (@lem4476546) (@lem4476545 A B K)). Qed.
Lemma lem4476556 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)) = (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)).
Proof. exact (eq_refl (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b))). Qed.
Lemma lem4476557 {A K : Type'} (x : K) (a : K) (y : A) : (term191 A K x a y) = (term191 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4476556 A K x a y b)). Qed.
Lemma lem4476558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476559 {A K : Type'} (x : K) (a : K) (y : A) : (term192 A K x a y) = (term192 A K x a y).
Proof. exact (MK_COMB (@lem4476558 A) (@lem4476557 A K x a y)). Qed.
Lemma lem4476560 {A K : Type'} (x : K) (y : A) : (term193 A K x y) = (term193 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4476559 A K x a y)). Qed.
Lemma lem4476561 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4476562 {A K : Type'} (x : K) (y : A) : (term194 A K x y) = (term194 A K x y).
Proof. exact (MK_COMB (@lem4476561 K) (@lem4476560 A K x y)). Qed.
Lemma lem4476563 {A K : Type'} (x : K) : (term195 A K x) = (term195 A K x).
Proof. exact (fun_ext (fun y : A => @lem4476562 A K x y)). Qed.
Lemma lem4476564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476565 {A K : Type'} (x : K) : (term196 A K x) = (term196 A K x).
Proof. exact (MK_COMB (@lem4476564 A) (@lem4476563 A K x)). Qed.
Lemma lem4476566 {A K : Type'} : (term197 A K) = (term197 A K).
Proof. exact (fun_ext (fun x : K => @lem4476565 A K x)). Qed.
Lemma lem4476567 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4476568 {A K : Type'} : (term153 A K) = (term153 A K).
Proof. exact (MK_COMB (@lem4476567 K) (@lem4476566 A K)). Qed.
Lemma lem4476569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4476570 {A K : Type'} : (term162 A K) = (term162 A K).
Proof. exact (MK_COMB (@lem4476569) (@lem4476568 A K)). Qed.
Lemma lem4476571 {A B K : Type'} : (term164 A B K) = (term164 A B K).
Proof. exact (MK_COMB (@lem4476570 A K) (@lem4476547 A B K)). Qed.
Lemma lem4476580 {A K : Type'} (x : A) (a : A) (y : prod K A) (b : prod K A) : (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b)) = (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b)).
Proof. exact (eq_refl (((@pair A (prod K A) x y) = (@pair A (prod K A) a b)) = (term198 A K x a y b))). Qed.
Lemma lem4476581 {A K : Type'} (x : A) (a : A) (y : prod K A) : (term199 A K x a y) = (term199 A K x a y).
Proof. exact (fun_ext (fun b : prod K A => @lem4476580 A K x a y b)). Qed.
Lemma lem4476582 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476583 {A K : Type'} (x : A) (a : A) (y : prod K A) : (term200 A K x a y) = (term200 A K x a y).
Proof. exact (MK_COMB (@lem4476582 A K) (@lem4476581 A K x a y)). Qed.
Lemma lem4476584 {A K : Type'} (x : A) (y : prod K A) : (term201 A K x y) = (term201 A K x y).
Proof. exact (fun_ext (fun a : A => @lem4476583 A K x a y)). Qed.
Lemma lem4476585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476586 {A K : Type'} (x : A) (y : prod K A) : (term202 A K x y) = (term202 A K x y).
Proof. exact (MK_COMB (@lem4476585 A) (@lem4476584 A K x y)). Qed.
Lemma lem4476587 {A K : Type'} (x : A) : (term203 A K x) = (term203 A K x).
Proof. exact (fun_ext (fun y : prod K A => @lem4476586 A K x y)). Qed.
Lemma lem4476588 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476589 {A K : Type'} (x : A) : (term204 A K x) = (term204 A K x).
Proof. exact (MK_COMB (@lem4476588 A K) (@lem4476587 A K x)). Qed.
Lemma lem4476590 {A K : Type'} : (term205 A K) = (term205 A K).
Proof. exact (fun_ext (fun x : A => @lem4476589 A K x)). Qed.
Lemma lem4476591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476592 {A K : Type'} : (term155 A K) = (term155 A K).
Proof. exact (MK_COMB (@lem4476591 A) (@lem4476590 A K)). Qed.
Lemma lem4476593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4476594 {A K : Type'} : (term165 A K) = (term165 A K).
Proof. exact (MK_COMB (@lem4476593) (@lem4476592 A K)). Qed.
Lemma lem4476595 {A B K : Type'} : (term167 A B K) = (term167 A B K).
Proof. exact (MK_COMB (@lem4476594 A K) (@lem4476571 A B K)). Qed.
Lemma lem4476608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4476609 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term141 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476608 A K k s t x i x')). Qed.
Lemma lem4476610 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476611 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term143 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4476610 A) (@lem4476609 A K k s t x i)). Qed.
Lemma lem4476612 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term145 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4476611 A K k s t x i)). Qed.
Lemma lem4476613 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476614 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term146 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4476613 K) (@lem4476612 A K k s t x)). Qed.
Lemma lem4476623 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term72 A K k t x i x')). Qed.
Lemma lem4476624 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term74 A K k t x i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476623 A K k t x i x')). Qed.
Lemma lem4476625 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476626 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term76 A K k t x i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4476625 A) (@lem4476624 A K k t x i)). Qed.
Lemma lem4476627 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term78 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4476626 A K k t x i)). Qed.
Lemma lem4476628 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476629 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4476628 K) (@lem4476627 A K k t x)). Qed.
Lemma lem4476638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term72 A K k s x i x')). Qed.
Lemma lem4476639 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term74 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4476638 A K k s x i x')). Qed.
Lemma lem4476640 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term76 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4476640 A) (@lem4476639 A K k s x i)). Qed.
Lemma lem4476642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term78 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4476641 A K k s x i)). Qed.
Lemma lem4476643 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term79 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4476643 K) (@lem4476642 A K k s x)). Qed.
Lemma lem4476645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4476646 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term81 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4476645) (@lem4476644 A K k s x)). Qed.
Lemma lem4476647 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4476646 A K k s x) (@lem4476629 A K k t x)). Qed.
Lemma lem4476648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4476649 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term84 A K s k t x) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4476648) (@lem4476647 A K s k t x)). Qed.
Lemma lem4476650 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term82 A K s k t x) = (term146 A K k s t x)) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (MK_COMB (@lem4476649 A K s k t x) (@lem4476614 A K k s t x)). Qed.
Lemma lem4476651 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term148 A K k s t) = (term148 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4476650 A K k s t x)). Qed.
Lemma lem4476652 {A K : Type'} : (@all (prod K A)) = (@all (prod K A)).
Proof. exact (eq_refl (@all (prod K A))). Qed.
Lemma lem4476653 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term149 A K k s t) = (term149 A K k s t).
Proof. exact (MK_COMB (@lem4476652 A K) (@lem4476651 A K k s t)). Qed.
Lemma lem4476654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476655 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term152 A K k s t).
Proof. exact (MK_COMB (@lem4476654) (@lem4476653 A K k s t)). Qed.
Lemma lem4476656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4476657 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term168 A K k s t) = (term168 A K k s t).
Proof. exact (MK_COMB (@lem4476656) (@lem4476655 A K k s t)). Qed.
Lemma lem4476658 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term169 A B K k s t) = (term169 A B K k s t).
Proof. exact (MK_COMB (@lem4476657 A K k s t) (@lem4476595 A B K)). Qed.
Lemma lem4476659 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term171 A B K s t) = (term171 A B K s t).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4476658 A B K k s t)). Qed.
Lemma lem4476660 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4476661 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term173 A B K s t) = (term173 A B K s t).
Proof. exact (MK_COMB (@lem4476660 K) (@lem4476659 A B K s t)). Qed.
Lemma lem4476662 {A B K : Type'} (t : type1470 A K) : (term175 A B K t) = (term175 A B K t).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4476661 A B K s t)). Qed.
Lemma lem4476663 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4476664 {A B K : Type'} (t : type1470 A K) : (term177 A B K t) = (term177 A B K t).
Proof. exact (MK_COMB (@lem4476663 A K) (@lem4476662 A B K t)). Qed.
Lemma lem4476665 {A B K : Type'} : (term179 A B K) = (term179 A B K).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4476664 A B K t)). Qed.
Lemma lem4476666 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4476667 {A B K : Type'} : (term181 A B K) = (term181 A B K).
Proof. exact (MK_COMB (@lem4476666 A K) (@lem4476665 A B K)). Qed.
Lemma lem4476830 {A B K : Type'} : (term180 A B K) = (term181 A B K).
Proof. exact (TRANS (@lem4476524 A B K) (@lem4476667 A B K)). Qed.
Lemma lem4476831 {A B K : Type'} : (term181 A B K) = (term180 A B K).
Proof. exact (SYM (@lem4476830 A B K)). Qed.
Lemma lem4476832 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term152 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4476834 {A K : Type'} (h1 : term153 A K) : term153 A K.
Proof. exact (h1). Qed.
Lemma lem4476844 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term206 A K k x s i) = (term207 A K k x s i).
Proof. exact (@lem17045 (@IN K i k) (term208 A K x s i)). Qed.
Lemma lem4476848 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4476850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4476851 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term210 A K k x s i) = (term211 A K k x s i).
Proof. exact (MK_COMB (@lem4476850) (@lem4476844 A K k x s i)). Qed.
Lemma lem4476852 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term212 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (MK_COMB (@lem4476851 A K k x' s i) (@lem4476848 A K x i x')). Qed.
Lemma lem4476853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k s x i x') = (term212 A K k s x i x').
Proof. exact (@lem17045 (term56 A K k x' s i) (x = (@pair K A i x'))). Qed.
Lemma lem4476854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (TRANS (@lem4476853 A K k s x i x') (@lem4476852 A K k s x i x')). Qed.
Lemma lem4476857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term72 A K k s x i x')). Qed.
Lemma lem4476858 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4476859 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term217 A K k s x i) = (term218 A K k s x i).
Proof. exact (@lem4476858 A (term74 A K k s x i)). Qed.
Lemma lem4476860 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4476861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476862 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k s x i x') = (term214 A K k s x i x').
Proof. exact (MK_COMB (@lem4476861) (@lem4476860 A K k s x i x')). Qed.
Lemma lem4476863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (TRANS (@lem4476862 A K k s x i x') (@lem4476854 A K k s x i x')). Qed.
Lemma lem4476864 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term221 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4476863 A K k s x i x')). Qed.
Lemma lem4476865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476866 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term218 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4476865 A) (@lem4476864 A K k s x i)). Qed.
Lemma lem4476867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term217 A K k s x i) = (term223 A K k s x i).
Proof. exact (TRANS (@lem4476859 A K k s x i) (@lem4476866 A K k s x i)). Qed.
Lemma lem4476868 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term74 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4476857 A K k s x i x')). Qed.
Lemma lem4476869 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476870 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term76 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4476869 A) (@lem4476868 A K k s x i)). Qed.
Lemma lem4476871 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4476872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term224 A K k s x) = (term225 A K k s x).
Proof. exact (@lem4476871 K (term78 A K k s x)). Qed.
Lemma lem4476873 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4476874 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term227 A K k s x i) = (term217 A K k s x i).
Proof. exact (MK_COMB (@lem4476874) (@lem4476873 A K k s x i)). Qed.
Lemma lem4476876 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term227 A K k s x i) = (term223 A K k s x i).
Proof. exact (TRANS (@lem4476875 A K k s x i) (@lem4476867 A K k s x i)). Qed.
Lemma lem4476877 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term228 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4476876 A K k s x i)). Qed.
Lemma lem4476878 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4476879 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term225 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4476878 K) (@lem4476877 A K k s x)). Qed.
Lemma lem4476880 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term224 A K k s x) = (term230 A K k s x).
Proof. exact (TRANS (@lem4476872 A K k s x) (@lem4476879 A K k s x)). Qed.
Lemma lem4476881 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term78 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4476870 A K k s x i)). Qed.
Lemma lem4476882 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476883 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term79 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4476882 K) (@lem4476881 A K k s x)). Qed.
Lemma lem4476892 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term206 A K k x t i) = (term207 A K k x t i).
Proof. exact (@lem17045 (@IN K i k) (term208 A K x t i)). Qed.
Lemma lem4476896 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4476898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4476899 {A K : Type'} (k : K -> Prop) (x : A) (t : type1470 A K) (i : K) : (term210 A K k x t i) = (term211 A K k x t i).
Proof. exact (MK_COMB (@lem4476898) (@lem4476892 A K k x t i)). Qed.
Lemma lem4476900 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term212 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (MK_COMB (@lem4476899 A K k x' t i) (@lem4476896 A K x i x')). Qed.
Lemma lem4476901 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k t x i x') = (term212 A K k t x i x').
Proof. exact (@lem17045 (term56 A K k x' t i) (x = (@pair K A i x'))). Qed.
Lemma lem4476902 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term214 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (TRANS (@lem4476901 A K k t x i x') (@lem4476900 A K k t x i x')). Qed.
Lemma lem4476905 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term72 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term72 A K k t x i x')). Qed.
Lemma lem4476906 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4476907 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term217 A K k t x i) = (term218 A K k t x i).
Proof. exact (@lem4476906 A (term74 A K k t x i)). Qed.
Lemma lem4476908 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k t x i x') = (term72 A K k t x i x').
Proof. exact (eq_refl (term219 A K k t x i x')). Qed.
Lemma lem4476909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476910 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k t x i x') = (term214 A K k t x i x').
Proof. exact (MK_COMB (@lem4476909) (@lem4476908 A K k t x i x')). Qed.
Lemma lem4476911 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term220 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (TRANS (@lem4476910 A K k t x i x') (@lem4476902 A K k t x i x')). Qed.
Lemma lem4476912 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term221 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476911 A K k t x i x')). Qed.
Lemma lem4476913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476914 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term218 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4476913 A) (@lem4476912 A K k t x i)). Qed.
Lemma lem4476915 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term217 A K k t x i) = (term223 A K k t x i).
Proof. exact (TRANS (@lem4476907 A K k t x i) (@lem4476914 A K k t x i)). Qed.
Lemma lem4476916 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term74 A K k t x i) = (term74 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476905 A K k t x i x')). Qed.
Lemma lem4476917 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476918 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term76 A K k t x i) = (term76 A K k t x i).
Proof. exact (MK_COMB (@lem4476917 A) (@lem4476916 A K k t x i)). Qed.
Lemma lem4476919 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4476920 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term224 A K k t x) = (term225 A K k t x).
Proof. exact (@lem4476919 K (term78 A K k t x)). Qed.
Lemma lem4476921 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term226 A K k t x i) = (term76 A K k t x i).
Proof. exact (eq_refl (term226 A K k t x i)). Qed.
Lemma lem4476922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476923 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term227 A K k t x i) = (term217 A K k t x i).
Proof. exact (MK_COMB (@lem4476922) (@lem4476921 A K k t x i)). Qed.
Lemma lem4476924 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term227 A K k t x i) = (term223 A K k t x i).
Proof. exact (TRANS (@lem4476923 A K k t x i) (@lem4476915 A K k t x i)). Qed.
Lemma lem4476925 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term228 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4476924 A K k t x i)). Qed.
Lemma lem4476926 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4476927 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term225 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4476926 K) (@lem4476925 A K k t x)). Qed.
Lemma lem4476928 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term224 A K k t x) = (term230 A K k t x).
Proof. exact (TRANS (@lem4476920 A K k t x) (@lem4476927 A K k t x)). Qed.
Lemma lem4476929 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term78 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4476918 A K k t x i)). Qed.
Lemma lem4476930 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476931 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4476930 K) (@lem4476929 A K k t x)). Qed.
Lemma lem4476932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4476933 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term231 A K k s x) = (term232 A K k s x).
Proof. exact (MK_COMB (@lem4476932) (@lem4476880 A K k s x)). Qed.
Lemma lem4476934 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term233 A K s k t x) = (term234 A K s k t x).
Proof. exact (MK_COMB (@lem4476933 A K k s x) (@lem4476928 A K k t x)). Qed.
Lemma lem4476935 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term235 A K s k t x) = (term233 A K s k t x).
Proof. exact (@lem17045 (term79 A K k s x) (term79 A K k t x)). Qed.
Lemma lem4476936 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term235 A K s k t x) = (term234 A K s k t x).
Proof. exact (TRANS (@lem4476935 A K s k t x) (@lem4476934 A K s k t x)). Qed.
Lemma lem4476937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4476938 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term81 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4476937) (@lem4476883 A K k s x)). Qed.
Lemma lem4476939 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4476938 A K k s x) (@lem4476931 A K k t x)). Qed.
Lemma lem4476950 {A K : Type'} (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term236 A K s x t i) = (term237 A K s x t i).
Proof. exact (@lem17045 (term208 A K x s i) (term208 A K x t i)). Qed.
Lemma lem4476955 {K : Type'} (i : K) (k : K -> Prop) : (term238 K i k) = (term238 K i k).
Proof. exact (eq_refl (term238 K i k)). Qed.
Lemma lem4476956 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term239 A K k s x t i) = (term240 A K k s x t i).
Proof. exact (MK_COMB (@lem4476955 K i k) (@lem4476950 A K s x t i)). Qed.
Lemma lem4476957 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term241 A K k s x t i) = (term239 A K k s x t i).
Proof. exact (@lem17045 (@IN K i k) (term96 A K s x t i)). Qed.
Lemma lem4476958 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term241 A K k s x t i) = (term240 A K k s x t i).
Proof. exact (TRANS (@lem4476957 A K k s x t i) (@lem4476956 A K k s x t i)). Qed.
Lemma lem4476962 {A K : Type'} (x : prod K A) (i : K) (x' : A) : (term209 A K x i x') = (term209 A K x i x').
Proof. exact (eq_refl (term209 A K x i x')). Qed.
Lemma lem4476964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4476965 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : A) (t : type1470 A K) (i : K) : (term242 A K k s x t i) = (term243 A K k s x t i).
Proof. exact (MK_COMB (@lem4476964) (@lem4476958 A K k s x t i)). Qed.
Lemma lem4476966 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term244 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (MK_COMB (@lem4476965 A K k s x' t i) (@lem4476962 A K x i x')). Qed.
Lemma lem4476967 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term246 A K k s t x i x') = (term244 A K k s t x i x').
Proof. exact (@lem17045 (term99 A K k s x' t i) (x = (@pair K A i x'))). Qed.
Lemma lem4476968 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term246 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (TRANS (@lem4476967 A K k s t x i x') (@lem4476966 A K k s t x i x')). Qed.
Lemma lem4476971 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4476972 {A : Type'} (P : A -> Prop) : (term215 A P) = (term216 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4476973 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term247 A K k s t x i) = (term248 A K k s t x i).
Proof. exact (@lem4476972 A (term141 A K k s t x i)). Qed.
Lemma lem4476974 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4476975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476976 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term250 A K k s t x i x') = (term246 A K k s t x i x').
Proof. exact (MK_COMB (@lem4476975) (@lem4476974 A K k s t x i x')). Qed.
Lemma lem4476977 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term250 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (TRANS (@lem4476976 A K k s t x i x') (@lem4476968 A K k s t x i x')). Qed.
Lemma lem4476978 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term251 A K k s t x i) = (term252 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476977 A K k s t x i x')). Qed.
Lemma lem4476979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4476980 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term248 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (MK_COMB (@lem4476979 A) (@lem4476978 A K k s t x i)). Qed.
Lemma lem4476981 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term247 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (TRANS (@lem4476973 A K k s t x i) (@lem4476980 A K k s t x i)). Qed.
Lemma lem4476982 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term141 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4476971 A K k s t x i x')). Qed.
Lemma lem4476983 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4476984 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term143 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4476983 A) (@lem4476982 A K k s t x i)). Qed.
Lemma lem4476985 {K : Type'} (P : K -> Prop) : (term215 K P) = (term216 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem4476986 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term254 A K k s t x) = (term255 A K k s t x).
Proof. exact (@lem4476985 K (term145 A K k s t x)). Qed.
Lemma lem4476987 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4476988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4476989 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term257 A K k s t x i) = (term247 A K k s t x i).
Proof. exact (MK_COMB (@lem4476988) (@lem4476987 A K k s t x i)). Qed.
Lemma lem4476990 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term257 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (TRANS (@lem4476989 A K k s t x i) (@lem4476981 A K k s t x i)). Qed.
Lemma lem4476991 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term258 A K k s t x) = (term259 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4476990 A K k s t x i)). Qed.
Lemma lem4476992 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4476993 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term255 A K k s t x) = (term260 A K k s t x).
Proof. exact (MK_COMB (@lem4476992 K) (@lem4476991 A K k s t x)). Qed.
Lemma lem4476994 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term254 A K k s t x) = (term260 A K k s t x).
Proof. exact (TRANS (@lem4476986 A K k s t x) (@lem4476993 A K k s t x)). Qed.
Lemma lem4476995 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term145 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4476984 A K k s t x i)). Qed.
Lemma lem4476996 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4476997 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term146 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4476996 K) (@lem4476995 A K k s t x)). Qed.
Lemma lem4476998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4476999 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term261 A K s k t x) = (term262 A K s k t x).
Proof. exact (MK_COMB (@lem4476998) (@lem4476936 A K s k t x)). Qed.
Lemma lem4477000 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term263 A K k s t x) = (term264 A K k s t x).
Proof. exact (MK_COMB (@lem4476999 A K s k t x) (@lem4476997 A K k s t x)). Qed.
Lemma lem4477001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477002 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term265 A K s k t x) = (term265 A K s k t x).
Proof. exact (MK_COMB (@lem4477001) (@lem4476939 A K s k t x)). Qed.
Lemma lem4477003 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term266 A K k s t x) = (term267 A K k s t x).
Proof. exact (MK_COMB (@lem4477002 A K s k t x) (@lem4476994 A K k s t x)). Qed.
Lemma lem4477004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477005 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term268 A K k s t x) = (term269 A K k s t x).
Proof. exact (MK_COMB (@lem4477004) (@lem4477003 A K k s t x)). Qed.
Lemma lem4477006 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term270 A K k s t x) = (term271 A K k s t x).
Proof. exact (MK_COMB (@lem4477005 A K k s t x) (@lem4477000 A K k s t x)). Qed.
Lemma lem4477007 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term272 A K k s t x) = (term270 A K k s t x).
Proof. exact (@lem17646 (term82 A K s k t x) (term146 A K k s t x)). Qed.
Lemma lem4477008 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term272 A K k s t x) = (term271 A K k s t x).
Proof. exact (TRANS (@lem4477007 A K k s t x) (@lem4477006 A K k s t x)). Qed.
Lemma lem4477009 {A K : Type'} (P : type1223 A K) : (term273 A K P) = (term274 A K P).
Proof. exact (@lem18392 (prod K A) P). Qed.
Lemma lem4477010 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term275 A K k s t).
Proof. exact (@lem4477009 A K (term148 A K k s t)). Qed.
Lemma lem4477011 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term276 A K k s t x) = ((term82 A K s k t x) = (term146 A K k s t x)).
Proof. exact (eq_refl (term276 A K k s t x)). Qed.
Lemma lem4477012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4477013 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term277 A K k s t x) = (term272 A K k s t x).
Proof. exact (MK_COMB (@lem4477012) (@lem4477011 A K k s t x)). Qed.
Lemma lem4477014 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term277 A K k s t x) = (term271 A K k s t x).
Proof. exact (TRANS (@lem4477013 A K k s t x) (@lem4477008 A K k s t x)). Qed.
Lemma lem4477015 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term278 A K k s t) = (term279 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477014 A K k s t x)). Qed.
Lemma lem4477016 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477017 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term275 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4477016 A K) (@lem4477015 A K k s t)). Qed.
Lemma lem4477018 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term280 A K k s t).
Proof. exact (TRANS (@lem4477010 A K k s t) (@lem4477017 A K k s t)). Qed.
Lemma lem4477020 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4477021 {A K : Type'} (P : type1223 A K) (Q : type1223 A K) : (term283 A K P Q) = (term284 A K P Q).
Proof. exact (@lem4477020 (prod K A) P Q). Qed.
Lemma lem4477022 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term286 A K k s t).
Proof. exact (@lem4477021 A K (term287 A K k s t) (term288 A K k s t)). Qed.
Lemma lem4477023 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term289 A K k s t x) = (term267 A K k s t x).
Proof. exact (eq_refl (term289 A K k s t x)). Qed.
Lemma lem4477024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477025 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term290 A K k s t x) = (term269 A K k s t x).
Proof. exact (MK_COMB (@lem4477024) (@lem4477023 A K k s t x)). Qed.
Lemma lem4477026 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term291 A K k s t x) = (term264 A K k s t x).
Proof. exact (eq_refl (term291 A K k s t x)). Qed.
Lemma lem4477027 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term292 A K k s t x) = (term271 A K k s t x).
Proof. exact (MK_COMB (@lem4477025 A K k s t x) (@lem4477026 A K k s t x)). Qed.
Lemma lem4477028 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term293 A K k s t) = (term279 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477027 A K k s t x)). Qed.
Lemma lem4477029 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477030 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4477029 A K) (@lem4477028 A K k s t)). Qed.
Lemma lem4477031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477032 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term294 A K k s t) = (term295 A K k s t).
Proof. exact (MK_COMB (@lem4477031) (@lem4477030 A K k s t)). Qed.
Lemma lem4477033 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term289 A K k s t x) = (term267 A K k s t x).
Proof. exact (eq_refl (term289 A K k s t x)). Qed.
Lemma lem4477034 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term296 A K k s t) = (term287 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477033 A K k s t x)). Qed.
Lemma lem4477035 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477036 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term297 A K k s t) = (term298 A K k s t).
Proof. exact (MK_COMB (@lem4477035 A K) (@lem4477034 A K k s t)). Qed.
Lemma lem4477037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477038 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term299 A K k s t) = (term300 A K k s t).
Proof. exact (MK_COMB (@lem4477037) (@lem4477036 A K k s t)). Qed.
Lemma lem4477039 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term291 A K k s t x) = (term264 A K k s t x).
Proof. exact (eq_refl (term291 A K k s t x)). Qed.
Lemma lem4477040 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term301 A K k s t) = (term288 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477039 A K k s t x)). Qed.
Lemma lem4477041 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477042 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term302 A K k s t) = (term303 A K k s t).
Proof. exact (MK_COMB (@lem4477041 A K) (@lem4477040 A K k s t)). Qed.
Lemma lem4477043 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term286 A K k s t) = (term304 A K k s t).
Proof. exact (MK_COMB (@lem4477038 A K k s t) (@lem4477042 A K k s t)). Qed.
Lemma lem4477044 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term285 A K k s t) = (term286 A K k s t)) = ((term280 A K k s t) = (term304 A K k s t)).
Proof. exact (MK_COMB (@lem4477032 A K k s t) (@lem4477043 A K k s t)). Qed.
Lemma lem4477045 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term304 A K k s t).
Proof. exact (EQ_MP (@lem4477044 A K k s t) (@lem4477022 A K k s t)). Qed.
Lemma lem4477455 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477456 {K : Type'} (P : K -> Prop) (Q : Prop) : (term305 K P Q) = (term306 K P Q).
Proof. exact (@lem4477455 K P Q). Qed.
Lemma lem4477457 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term307 A K s k t x) = (term308 A K s k t x).
Proof. exact (@lem4477456 K (term78 A K k s x) (term79 A K k t x)). Qed.
Lemma lem4477458 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4477459 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term309 A K k s x) = (term78 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4477458 A K k s x i)). Qed.
Lemma lem4477460 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477461 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term310 A K k s x) = (term79 A K k s x).
Proof. exact (MK_COMB (@lem4477460 K) (@lem4477459 A K k s x)). Qed.
Lemma lem4477462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477463 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term311 A K k s x) = (term81 A K k s x).
Proof. exact (MK_COMB (@lem4477462) (@lem4477461 A K k s x)). Qed.
Lemma lem4477464 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (eq_refl (term79 A K k t x)). Qed.
Lemma lem4477465 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term307 A K s k t x) = (term82 A K s k t x).
Proof. exact (MK_COMB (@lem4477463 A K k s x) (@lem4477464 A K k t x)). Qed.
Lemma lem4477466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477467 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term312 A K s k t x) = (term84 A K s k t x).
Proof. exact (MK_COMB (@lem4477466) (@lem4477465 A K s k t x)). Qed.
Lemma lem4477468 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term226 A K k s x i) = (term76 A K k s x i).
Proof. exact (eq_refl (term226 A K k s x i)). Qed.
Lemma lem4477469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477470 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term313 A K k s x i) = (term314 A K k s x i).
Proof. exact (MK_COMB (@lem4477469) (@lem4477468 A K k s x i)). Qed.
Lemma lem4477471 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (eq_refl (term79 A K k t x)). Qed.
Lemma lem4477472 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term315 A K s i k t x) = (term316 A K s i k t x).
Proof. exact (MK_COMB (@lem4477470 A K k s x i) (@lem4477471 A K k t x)). Qed.
Lemma lem4477473 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term317 A K s k t x) = (term318 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4477472 A K s i k t x)). Qed.
Lemma lem4477474 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477475 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term308 A K s k t x) = (term319 A K s k t x).
Proof. exact (MK_COMB (@lem4477474 K) (@lem4477473 A K s k t x)). Qed.
Lemma lem4477476 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : ((term307 A K s k t x) = (term308 A K s k t x)) = ((term82 A K s k t x) = (term319 A K s k t x)).
Proof. exact (MK_COMB (@lem4477467 A K s k t x) (@lem4477475 A K s k t x)). Qed.
Lemma lem4477477 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term319 A K s k t x).
Proof. exact (EQ_MP (@lem4477476 A K s k t x) (@lem4477457 A K s k t x)). Qed.
Lemma lem4477479 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477480 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (@lem4477479 A P Q). Qed.
Lemma lem4477481 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term320 A K s i k t x) = (term321 A K s i k t x).
Proof. exact (@lem4477480 A (term74 A K k s x i) (term79 A K k t x)). Qed.
Lemma lem4477482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4477483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term322 A K k s x i) = (term74 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4477482 A K k s x i x')). Qed.
Lemma lem4477484 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477485 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term323 A K k s x i) = (term76 A K k s x i).
Proof. exact (MK_COMB (@lem4477484 A) (@lem4477483 A K k s x i)). Qed.
Lemma lem4477486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477487 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term324 A K k s x i) = (term314 A K k s x i).
Proof. exact (MK_COMB (@lem4477486) (@lem4477485 A K k s x i)). Qed.
Lemma lem4477488 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (eq_refl (term79 A K k t x)). Qed.
Lemma lem4477489 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term320 A K s i k t x) = (term316 A K s i k t x).
Proof. exact (MK_COMB (@lem4477487 A K k s x i) (@lem4477488 A K k t x)). Qed.
Lemma lem4477490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477491 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term325 A K s i k t x) = (term326 A K s i k t x).
Proof. exact (MK_COMB (@lem4477490) (@lem4477489 A K s i k t x)). Qed.
Lemma lem4477492 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term219 A K k s x i x') = (term72 A K k s x i x').
Proof. exact (eq_refl (term219 A K k s x i x')). Qed.
Lemma lem4477493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477494 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term327 A K k s x i x') = (term328 A K k s x i x').
Proof. exact (MK_COMB (@lem4477493) (@lem4477492 A K k s x i x')). Qed.
Lemma lem4477495 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term79 A K k t x) = (term79 A K k t x).
Proof. exact (eq_refl (term79 A K k t x)). Qed.
Lemma lem4477496 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term329 A K s i x k t x') = (term330 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477494 A K k s x' i x) (@lem4477495 A K k t x')). Qed.
Lemma lem4477497 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term331 A K s i k t x) = (term332 A K s i k t x).
Proof. exact (fun_ext (fun x' : A => @lem4477496 A K s i x' k t x)). Qed.
Lemma lem4477498 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477499 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term321 A K s i k t x) = (term333 A K s i k t x).
Proof. exact (MK_COMB (@lem4477498 A) (@lem4477497 A K s i k t x)). Qed.
Lemma lem4477500 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : ((term320 A K s i k t x) = (term321 A K s i k t x)) = ((term316 A K s i k t x) = (term333 A K s i k t x)).
Proof. exact (MK_COMB (@lem4477491 A K s i k t x) (@lem4477499 A K s i k t x)). Qed.
Lemma lem4477501 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term316 A K s i k t x) = (term333 A K s i k t x).
Proof. exact (EQ_MP (@lem4477500 A K s i k t x) (@lem4477481 A K s i k t x)). Qed.
Lemma lem4477503 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4477504 {K : Type'} (P : Prop) (Q : K -> Prop) : (term334 K P Q) = (term335 K P Q).
Proof. exact (@lem4477503 K P Q). Qed.
Lemma lem4477505 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term336 A K s i x k t x') = (term337 A K s i x k t x').
Proof. exact (@lem4477504 K (term72 A K k s x' i x) (term78 A K k t x')). Qed.
Lemma lem4477506 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term226 A K k t x i) = (term76 A K k t x i).
Proof. exact (eq_refl (term226 A K k t x i)). Qed.
Lemma lem4477507 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term309 A K k t x) = (term78 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4477506 A K k t x i)). Qed.
Lemma lem4477508 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477509 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term310 A K k t x) = (term79 A K k t x).
Proof. exact (MK_COMB (@lem4477508 K) (@lem4477507 A K k t x)). Qed.
Lemma lem4477510 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term328 A K k s x i x') = (term328 A K k s x i x').
Proof. exact (eq_refl (term328 A K k s x i x')). Qed.
Lemma lem4477511 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term336 A K s i x k t x') = (term330 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477510 A K k s x' i x) (@lem4477509 A K k t x')). Qed.
Lemma lem4477512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477513 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term338 A K s i x k t x') = (term339 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477512) (@lem4477511 A K s i x k t x')). Qed.
Lemma lem4477514 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) : (term226 A K k t x i') = (term76 A K k t x i').
Proof. exact (eq_refl (term226 A K k t x i')). Qed.
Lemma lem4477515 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term328 A K k s x i x') = (term328 A K k s x i x').
Proof. exact (eq_refl (term328 A K k s x i x')). Qed.
Lemma lem4477516 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term340 A K s i x k t x' i') = (term341 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477515 A K k s x' i x) (@lem4477514 A K k t x' i')). Qed.
Lemma lem4477517 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term342 A K s i x k t x') = (term343 A K s i x k t x').
Proof. exact (fun_ext (fun i' : K => @lem4477516 A K s i x k t x' i')). Qed.
Lemma lem4477518 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477519 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term337 A K s i x k t x') = (term344 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477518 K) (@lem4477517 A K s i x k t x')). Qed.
Lemma lem4477520 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : ((term336 A K s i x k t x') = (term337 A K s i x k t x')) = ((term330 A K s i x k t x') = (term344 A K s i x k t x')).
Proof. exact (MK_COMB (@lem4477513 A K s i x k t x') (@lem4477519 A K s i x k t x')). Qed.
Lemma lem4477521 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term330 A K s i x k t x') = (term344 A K s i x k t x').
Proof. exact (EQ_MP (@lem4477520 A K s i x k t x') (@lem4477505 A K s i x k t x')). Qed.
Lemma lem4477523 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4477524 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem4477523 A P Q). Qed.
Lemma lem4477525 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term345 A K s i x k t x' i') = (term346 A K s i x k t x' i').
Proof. exact (@lem4477524 A (term72 A K k s x' i x) (term74 A K k t x' i')). Qed.
Lemma lem4477526 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) (x' : A) : (term219 A K k t x i' x') = (term72 A K k t x i' x').
Proof. exact (eq_refl (term219 A K k t x i' x')). Qed.
Lemma lem4477527 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) : (term322 A K k t x i') = (term74 A K k t x i').
Proof. exact (fun_ext (fun x' : A => @lem4477526 A K k t x i' x')). Qed.
Lemma lem4477528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477529 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) : (term323 A K k t x i') = (term76 A K k t x i').
Proof. exact (MK_COMB (@lem4477528 A) (@lem4477527 A K k t x i')). Qed.
Lemma lem4477530 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term328 A K k s x i x') = (term328 A K k s x i x').
Proof. exact (eq_refl (term328 A K k s x i x')). Qed.
Lemma lem4477531 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term345 A K s i x k t x' i') = (term341 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477530 A K k s x' i x) (@lem4477529 A K k t x' i')). Qed.
Lemma lem4477532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477533 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term347 A K s i x k t x' i') = (term348 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477532) (@lem4477531 A K s i x k t x' i')). Qed.
Lemma lem4477534 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) (x' : A) : (term219 A K k t x i' x') = (term72 A K k t x i' x').
Proof. exact (eq_refl (term219 A K k t x i' x')). Qed.
Lemma lem4477535 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term328 A K k s x i x') = (term328 A K k s x i x').
Proof. exact (eq_refl (term328 A K k s x i x')). Qed.
Lemma lem4477536 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) (x'' : A) : (term349 A K s i x k t x' i' x'') = (term350 A K s i x k t x' i' x'').
Proof. exact (MK_COMB (@lem4477535 A K k s x' i x) (@lem4477534 A K k t x' i' x'')). Qed.
Lemma lem4477537 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term351 A K s i x k t x' i') = (term352 A K s i x k t x' i').
Proof. exact (fun_ext (fun x'' : A => @lem4477536 A K s i x k t x' i' x'')). Qed.
Lemma lem4477538 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477539 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term346 A K s i x k t x' i') = (term353 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477538 A) (@lem4477537 A K s i x k t x' i')). Qed.
Lemma lem4477540 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : ((term345 A K s i x k t x' i') = (term346 A K s i x k t x' i')) = ((term341 A K s i x k t x' i') = (term353 A K s i x k t x' i')).
Proof. exact (MK_COMB (@lem4477533 A K s i x k t x' i') (@lem4477539 A K s i x k t x' i')). Qed.
Lemma lem4477541 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term341 A K s i x k t x' i') = (term353 A K s i x k t x' i').
Proof. exact (EQ_MP (@lem4477540 A K s i x k t x' i') (@lem4477525 A K s i x k t x' i')). Qed.
Lemma lem4477542 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term343 A K s i x k t x') = (term354 A K s i x k t x').
Proof. exact (fun_ext (fun i' : K => @lem4477541 A K s i x k t x' i')). Qed.
Lemma lem4477543 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477544 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term344 A K s i x k t x') = (term355 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477543 K) (@lem4477542 A K s i x k t x')). Qed.
Lemma lem4477545 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term330 A K s i x k t x') = (term355 A K s i x k t x').
Proof. exact (TRANS (@lem4477521 A K s i x k t x') (@lem4477544 A K s i x k t x')). Qed.
Lemma lem4477546 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term332 A K s i k t x) = (term356 A K s i k t x).
Proof. exact (fun_ext (fun x' : A => @lem4477545 A K s i x' k t x)). Qed.
Lemma lem4477547 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477548 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term333 A K s i k t x) = (term357 A K s i k t x).
Proof. exact (MK_COMB (@lem4477547 A) (@lem4477546 A K s i k t x)). Qed.
Lemma lem4477549 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term316 A K s i k t x) = (term357 A K s i k t x).
Proof. exact (TRANS (@lem4477501 A K s i k t x) (@lem4477548 A K s i k t x)). Qed.
Lemma lem4477550 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term318 A K s k t x) = (term358 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4477549 A K s i k t x)). Qed.
Lemma lem4477551 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477552 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term319 A K s k t x) = (term359 A K s k t x).
Proof. exact (MK_COMB (@lem4477551 K) (@lem4477550 A K s k t x)). Qed.
Lemma lem4477553 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term82 A K s k t x) = (term359 A K s k t x).
Proof. exact (TRANS (@lem4477477 A K s k t x) (@lem4477552 A K s k t x)). Qed.
Lemma lem4477554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477555 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term265 A K s k t x) = (term360 A K s k t x).
Proof. exact (MK_COMB (@lem4477554) (@lem4477553 A K s k t x)). Qed.
Lemma lem4477556 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477557 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term267 A K k s t x) = (term361 A K k s t x).
Proof. exact (MK_COMB (@lem4477555 A K s k t x) (@lem4477556 A K k s t x)). Qed.
Lemma lem4477559 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477560 {K : Type'} (P : K -> Prop) (Q : Prop) : (term305 K P Q) = (term306 K P Q).
Proof. exact (@lem4477559 K P Q). Qed.
Lemma lem4477561 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term362 A K k s t x) = (term363 A K k s t x).
Proof. exact (@lem4477560 K (term358 A K s k t x) (term260 A K k s t x)). Qed.
Lemma lem4477562 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term364 A K s k t x i) = (term357 A K s i k t x).
Proof. exact (eq_refl (term364 A K s k t x i)). Qed.
Lemma lem4477563 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term365 A K s k t x) = (term358 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4477562 A K s i k t x)). Qed.
Lemma lem4477564 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477565 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term366 A K s k t x) = (term359 A K s k t x).
Proof. exact (MK_COMB (@lem4477564 K) (@lem4477563 A K s k t x)). Qed.
Lemma lem4477566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477567 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term367 A K s k t x) = (term360 A K s k t x).
Proof. exact (MK_COMB (@lem4477566) (@lem4477565 A K s k t x)). Qed.
Lemma lem4477568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477569 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term362 A K k s t x) = (term361 A K k s t x).
Proof. exact (MK_COMB (@lem4477567 A K s k t x) (@lem4477568 A K k s t x)). Qed.
Lemma lem4477570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477571 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term368 A K k s t x) = (term369 A K k s t x).
Proof. exact (MK_COMB (@lem4477570) (@lem4477569 A K k s t x)). Qed.
Lemma lem4477572 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term364 A K s k t x i) = (term357 A K s i k t x).
Proof. exact (eq_refl (term364 A K s k t x i)). Qed.
Lemma lem4477573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477574 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term370 A K s k t x i) = (term371 A K s i k t x).
Proof. exact (MK_COMB (@lem4477573) (@lem4477572 A K s i k t x)). Qed.
Lemma lem4477575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477576 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term372 A K i k s t x) = (term373 A K i k s t x).
Proof. exact (MK_COMB (@lem4477574 A K s i k t x) (@lem4477575 A K k s t x)). Qed.
Lemma lem4477577 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term374 A K k s t x) = (term375 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477576 A K i k s t x)). Qed.
Lemma lem4477578 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477579 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term363 A K k s t x) = (term376 A K k s t x).
Proof. exact (MK_COMB (@lem4477578 K) (@lem4477577 A K k s t x)). Qed.
Lemma lem4477580 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term362 A K k s t x) = (term363 A K k s t x)) = ((term361 A K k s t x) = (term376 A K k s t x)).
Proof. exact (MK_COMB (@lem4477571 A K k s t x) (@lem4477579 A K k s t x)). Qed.
Lemma lem4477581 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term361 A K k s t x) = (term376 A K k s t x).
Proof. exact (EQ_MP (@lem4477580 A K k s t x) (@lem4477561 A K k s t x)). Qed.
Lemma lem4477583 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477584 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (@lem4477583 A P Q). Qed.
Lemma lem4477585 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term377 A K i k s t x) = (term378 A K i k s t x).
Proof. exact (@lem4477584 A (term356 A K s i k t x) (term260 A K k s t x)). Qed.
Lemma lem4477586 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term379 A K s i k t x' x) = (term355 A K s i x k t x').
Proof. exact (eq_refl (term379 A K s i k t x' x)). Qed.
Lemma lem4477587 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term380 A K s i k t x) = (term356 A K s i k t x).
Proof. exact (fun_ext (fun x' : A => @lem4477586 A K s i x' k t x)). Qed.
Lemma lem4477588 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477589 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term381 A K s i k t x) = (term357 A K s i k t x).
Proof. exact (MK_COMB (@lem4477588 A) (@lem4477587 A K s i k t x)). Qed.
Lemma lem4477590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477591 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term382 A K s i k t x) = (term371 A K s i k t x).
Proof. exact (MK_COMB (@lem4477590) (@lem4477589 A K s i k t x)). Qed.
Lemma lem4477592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477593 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term377 A K i k s t x) = (term373 A K i k s t x).
Proof. exact (MK_COMB (@lem4477591 A K s i k t x) (@lem4477592 A K k s t x)). Qed.
Lemma lem4477594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477595 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term383 A K i k s t x) = (term384 A K i k s t x).
Proof. exact (MK_COMB (@lem4477594) (@lem4477593 A K i k s t x)). Qed.
Lemma lem4477596 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term379 A K s i k t x' x) = (term355 A K s i x k t x').
Proof. exact (eq_refl (term379 A K s i k t x' x)). Qed.
Lemma lem4477597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477598 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term385 A K s i k t x' x) = (term386 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477597) (@lem4477596 A K s i x k t x')). Qed.
Lemma lem4477599 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477600 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term387 A K i x k s t x') = (term388 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477598 A K s i x k t x') (@lem4477599 A K k s t x')). Qed.
Lemma lem4477601 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term389 A K i k s t x) = (term390 A K i k s t x).
Proof. exact (fun_ext (fun x' : A => @lem4477600 A K i x' k s t x)). Qed.
Lemma lem4477602 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477603 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term378 A K i k s t x) = (term391 A K i k s t x).
Proof. exact (MK_COMB (@lem4477602 A) (@lem4477601 A K i k s t x)). Qed.
Lemma lem4477604 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term377 A K i k s t x) = (term378 A K i k s t x)) = ((term373 A K i k s t x) = (term391 A K i k s t x)).
Proof. exact (MK_COMB (@lem4477595 A K i k s t x) (@lem4477603 A K i k s t x)). Qed.
Lemma lem4477605 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term373 A K i k s t x) = (term391 A K i k s t x).
Proof. exact (EQ_MP (@lem4477604 A K i k s t x) (@lem4477585 A K i k s t x)). Qed.
Lemma lem4477607 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477608 {K : Type'} (P : K -> Prop) (Q : Prop) : (term305 K P Q) = (term306 K P Q).
Proof. exact (@lem4477607 K P Q). Qed.
Lemma lem4477609 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term392 A K i x k s t x') = (term393 A K i x k s t x').
Proof. exact (@lem4477608 K (term354 A K s i x k t x') (term260 A K k s t x')). Qed.
Lemma lem4477610 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term394 A K s i x k t x' i') = (term353 A K s i x k t x' i').
Proof. exact (eq_refl (term394 A K s i x k t x' i')). Qed.
Lemma lem4477611 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term395 A K s i x k t x') = (term354 A K s i x k t x').
Proof. exact (fun_ext (fun i' : K => @lem4477610 A K s i x k t x' i')). Qed.
Lemma lem4477612 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477613 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term396 A K s i x k t x') = (term355 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477612 K) (@lem4477611 A K s i x k t x')). Qed.
Lemma lem4477614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477615 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) : (term397 A K s i x k t x') = (term386 A K s i x k t x').
Proof. exact (MK_COMB (@lem4477614) (@lem4477613 A K s i x k t x')). Qed.
Lemma lem4477616 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477617 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term392 A K i x k s t x') = (term388 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477615 A K s i x k t x') (@lem4477616 A K k s t x')). Qed.
Lemma lem4477618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477619 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term398 A K i x k s t x') = (term399 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477618) (@lem4477617 A K i x k s t x')). Qed.
Lemma lem4477620 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term394 A K s i x k t x' i') = (term353 A K s i x k t x' i').
Proof. exact (eq_refl (term394 A K s i x k t x' i')). Qed.
Lemma lem4477621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477622 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term400 A K s i x k t x' i') = (term401 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477621) (@lem4477620 A K s i x k t x' i')). Qed.
Lemma lem4477623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477624 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term402 A K i x i' k s t x') = (term403 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477622 A K s i x k t x' i') (@lem4477623 A K k s t x')). Qed.
Lemma lem4477625 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term404 A K i x k s t x') = (term405 A K i x k s t x').
Proof. exact (fun_ext (fun i' : K => @lem4477624 A K i x i' k s t x')). Qed.
Lemma lem4477626 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477627 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term393 A K i x k s t x') = (term406 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477626 K) (@lem4477625 A K i x k s t x')). Qed.
Lemma lem4477628 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : ((term392 A K i x k s t x') = (term393 A K i x k s t x')) = ((term388 A K i x k s t x') = (term406 A K i x k s t x')).
Proof. exact (MK_COMB (@lem4477619 A K i x k s t x') (@lem4477627 A K i x k s t x')). Qed.
Lemma lem4477629 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term388 A K i x k s t x') = (term406 A K i x k s t x').
Proof. exact (EQ_MP (@lem4477628 A K i x k s t x') (@lem4477609 A K i x k s t x')). Qed.
Lemma lem4477631 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4477632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (@lem4477631 A P Q). Qed.
Lemma lem4477633 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term407 A K i x i' k s t x') = (term408 A K i x i' k s t x').
Proof. exact (@lem4477632 A (term352 A K s i x k t x' i') (term260 A K k s t x')). Qed.
Lemma lem4477634 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) (x'' : A) : (term409 A K s i x k t x' i' x'') = (term350 A K s i x k t x' i' x'').
Proof. exact (eq_refl (term409 A K s i x k t x' i' x'')). Qed.
Lemma lem4477635 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term410 A K s i x k t x' i') = (term352 A K s i x k t x' i').
Proof. exact (fun_ext (fun x'' : A => @lem4477634 A K s i x k t x' i' x'')). Qed.
Lemma lem4477636 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477637 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term411 A K s i x k t x' i') = (term353 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477636 A) (@lem4477635 A K s i x k t x' i')). Qed.
Lemma lem4477638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477639 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) : (term412 A K s i x k t x' i') = (term401 A K s i x k t x' i').
Proof. exact (MK_COMB (@lem4477638) (@lem4477637 A K s i x k t x' i')). Qed.
Lemma lem4477640 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477641 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term407 A K i x i' k s t x') = (term403 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477639 A K s i x k t x' i') (@lem4477640 A K k s t x')). Qed.
Lemma lem4477642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477643 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term413 A K i x i' k s t x') = (term414 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477642) (@lem4477641 A K i x i' k s t x')). Qed.
Lemma lem4477644 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) (x'' : A) : (term409 A K s i x k t x' i' x'') = (term350 A K s i x k t x' i' x'').
Proof. exact (eq_refl (term409 A K s i x k t x' i' x'')). Qed.
Lemma lem4477645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4477646 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (x' : prod K A) (i' : K) (x'' : A) : (term415 A K s i x k t x' i' x'') = (term416 A K s i x k t x' i' x'').
Proof. exact (MK_COMB (@lem4477645) (@lem4477644 A K s i x k t x' i' x'')). Qed.
Lemma lem4477647 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (eq_refl (term260 A K k s t x)). Qed.
Lemma lem4477648 {A K : Type'} (i : K) (x : A) (i' : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x'' : prod K A) : (term417 A K i x i' x' k s t x'') = (term418 A K i x i' x' k s t x'').
Proof. exact (MK_COMB (@lem4477646 A K s i x k t x'' i' x') (@lem4477647 A K k s t x'')). Qed.
Lemma lem4477649 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term419 A K i x i' k s t x') = (term420 A K i x i' k s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4477648 A K i x i' x'' k s t x')). Qed.
Lemma lem4477650 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477651 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term408 A K i x i' k s t x') = (term421 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477650 A) (@lem4477649 A K i x i' k s t x')). Qed.
Lemma lem4477652 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : ((term407 A K i x i' k s t x') = (term408 A K i x i' k s t x')) = ((term403 A K i x i' k s t x') = (term421 A K i x i' k s t x')).
Proof. exact (MK_COMB (@lem4477643 A K i x i' k s t x') (@lem4477651 A K i x i' k s t x')). Qed.
Lemma lem4477653 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term403 A K i x i' k s t x') = (term421 A K i x i' k s t x').
Proof. exact (EQ_MP (@lem4477652 A K i x i' k s t x') (@lem4477633 A K i x i' k s t x')). Qed.
Lemma lem4477654 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term405 A K i x k s t x') = (term422 A K i x k s t x').
Proof. exact (fun_ext (fun i' : K => @lem4477653 A K i x i' k s t x')). Qed.
Lemma lem4477655 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477656 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term406 A K i x k s t x') = (term423 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477655 K) (@lem4477654 A K i x k s t x')). Qed.
Lemma lem4477657 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term388 A K i x k s t x') = (term423 A K i x k s t x').
Proof. exact (TRANS (@lem4477629 A K i x k s t x') (@lem4477656 A K i x k s t x')). Qed.
Lemma lem4477658 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term390 A K i k s t x) = (term424 A K i k s t x).
Proof. exact (fun_ext (fun x' : A => @lem4477657 A K i x' k s t x)). Qed.
Lemma lem4477659 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477660 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term391 A K i k s t x) = (term425 A K i k s t x).
Proof. exact (MK_COMB (@lem4477659 A) (@lem4477658 A K i k s t x)). Qed.
Lemma lem4477661 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term373 A K i k s t x) = (term425 A K i k s t x).
Proof. exact (TRANS (@lem4477605 A K i k s t x) (@lem4477660 A K i k s t x)). Qed.
Lemma lem4477662 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term375 A K k s t x) = (term426 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477661 A K i k s t x)). Qed.
Lemma lem4477663 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477664 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term376 A K k s t x) = (term427 A K k s t x).
Proof. exact (MK_COMB (@lem4477663 K) (@lem4477662 A K k s t x)). Qed.
Lemma lem4477665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term361 A K k s t x) = (term427 A K k s t x).
Proof. exact (TRANS (@lem4477581 A K k s t x) (@lem4477664 A K k s t x)). Qed.
Lemma lem4477666 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term267 A K k s t x) = (term427 A K k s t x).
Proof. exact (TRANS (@lem4477557 A K k s t x) (@lem4477665 A K k s t x)). Qed.
Lemma lem4477667 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term287 A K k s t) = (term428 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477666 A K k s t x)). Qed.
Lemma lem4477668 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477669 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term298 A K k s t) = (term429 A K k s t).
Proof. exact (MK_COMB (@lem4477668 A K) (@lem4477667 A K k s t)). Qed.
Lemma lem4477670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477671 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term300 A K k s t) = (term430 A K k s t).
Proof. exact (MK_COMB (@lem4477670) (@lem4477669 A K k s t)). Qed.
Lemma lem4477673 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4477674 {K : Type'} (P : Prop) (Q : K -> Prop) : (term334 K P Q) = (term335 K P Q).
Proof. exact (@lem4477673 K P Q). Qed.
Lemma lem4477675 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term431 A K k s t x) = (term432 A K k s t x).
Proof. exact (@lem4477674 K (term234 A K s k t x) (term145 A K k s t x)). Qed.
Lemma lem4477676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4477677 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term433 A K k s t x) = (term145 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477676 A K k s t x i)). Qed.
Lemma lem4477678 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term434 A K k s t x) = (term146 A K k s t x).
Proof. exact (MK_COMB (@lem4477678 K) (@lem4477677 A K k s t x)). Qed.
Lemma lem4477680 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4477681 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term431 A K k s t x) = (term264 A K k s t x).
Proof. exact (MK_COMB (@lem4477680 A K s k t x) (@lem4477679 A K k s t x)). Qed.
Lemma lem4477682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477683 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term435 A K k s t x) = (term436 A K k s t x).
Proof. exact (MK_COMB (@lem4477682) (@lem4477681 A K k s t x)). Qed.
Lemma lem4477684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term256 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (eq_refl (term256 A K k s t x i)). Qed.
Lemma lem4477685 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4477686 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term437 A K k s t x i) = (term438 A K k s t x i).
Proof. exact (MK_COMB (@lem4477685 A K s k t x) (@lem4477684 A K k s t x i)). Qed.
Lemma lem4477687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term439 A K k s t x) = (term440 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477686 A K k s t x i)). Qed.
Lemma lem4477688 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477689 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term432 A K k s t x) = (term441 A K k s t x).
Proof. exact (MK_COMB (@lem4477688 K) (@lem4477687 A K k s t x)). Qed.
Lemma lem4477690 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term431 A K k s t x) = (term432 A K k s t x)) = ((term264 A K k s t x) = (term441 A K k s t x)).
Proof. exact (MK_COMB (@lem4477683 A K k s t x) (@lem4477689 A K k s t x)). Qed.
Lemma lem4477691 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term264 A K k s t x) = (term441 A K k s t x).
Proof. exact (EQ_MP (@lem4477690 A K k s t x) (@lem4477675 A K k s t x)). Qed.
Lemma lem4477693 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4477694 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem4477693 A P Q). Qed.
Lemma lem4477695 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term442 A K k s t x i) = (term443 A K k s t x i).
Proof. exact (@lem4477694 A (term234 A K s k t x) (term141 A K k s t x i)). Qed.
Lemma lem4477696 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4477697 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term444 A K k s t x i) = (term141 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4477696 A K k s t x i x')). Qed.
Lemma lem4477698 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477699 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term445 A K k s t x i) = (term143 A K k s t x i).
Proof. exact (MK_COMB (@lem4477698 A) (@lem4477697 A K k s t x i)). Qed.
Lemma lem4477700 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4477701 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term442 A K k s t x i) = (term438 A K k s t x i).
Proof. exact (MK_COMB (@lem4477700 A K s k t x) (@lem4477699 A K k s t x i)). Qed.
Lemma lem4477702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477703 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term446 A K k s t x i) = (term447 A K k s t x i).
Proof. exact (MK_COMB (@lem4477702) (@lem4477701 A K k s t x i)). Qed.
Lemma lem4477704 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term249 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term249 A K k s t x i x')). Qed.
Lemma lem4477705 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (eq_refl (term262 A K s k t x)). Qed.
Lemma lem4477706 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term448 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477705 A K s k t x) (@lem4477704 A K k s t x i x')). Qed.
Lemma lem4477707 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term450 A K k s t x i) = (term451 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4477706 A K k s t x i x')). Qed.
Lemma lem4477708 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477709 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term443 A K k s t x i) = (term452 A K k s t x i).
Proof. exact (MK_COMB (@lem4477708 A) (@lem4477707 A K k s t x i)). Qed.
Lemma lem4477710 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : ((term442 A K k s t x i) = (term443 A K k s t x i)) = ((term438 A K k s t x i) = (term452 A K k s t x i)).
Proof. exact (MK_COMB (@lem4477703 A K k s t x i) (@lem4477709 A K k s t x i)). Qed.
Lemma lem4477711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term438 A K k s t x i) = (term452 A K k s t x i).
Proof. exact (EQ_MP (@lem4477710 A K k s t x i) (@lem4477695 A K k s t x i)). Qed.
Lemma lem4477712 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term440 A K k s t x) = (term453 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477711 A K k s t x i)). Qed.
Lemma lem4477713 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477714 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term441 A K k s t x) = (term454 A K k s t x).
Proof. exact (MK_COMB (@lem4477713 K) (@lem4477712 A K k s t x)). Qed.
Lemma lem4477715 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term264 A K k s t x) = (term454 A K k s t x).
Proof. exact (TRANS (@lem4477691 A K k s t x) (@lem4477714 A K k s t x)). Qed.
Lemma lem4477716 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term288 A K k s t) = (term455 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477715 A K k s t x)). Qed.
Lemma lem4477717 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477718 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term303 A K k s t) = (term456 A K k s t).
Proof. exact (MK_COMB (@lem4477717 A K) (@lem4477716 A K k s t)). Qed.
Lemma lem4477719 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K k s t) = (term457 A K k s t).
Proof. exact (MK_COMB (@lem4477671 A K k s t) (@lem4477718 A K k s t)). Qed.
Lemma lem4477721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4477722 {A K : Type'} (P : type1223 A K) (Q : type1223 A K) : (term284 A K P Q) = (term283 A K P Q).
Proof. exact (@lem4477721 (prod K A) P Q). Qed.
Lemma lem4477723 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term458 A K k s t) = (term459 A K k s t).
Proof. exact (@lem4477722 A K (term428 A K k s t) (term455 A K k s t)). Qed.
Lemma lem4477724 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term460 A K k s t x) = (term427 A K k s t x).
Proof. exact (eq_refl (term460 A K k s t x)). Qed.
Lemma lem4477725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term461 A K k s t) = (term428 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477724 A K k s t x)). Qed.
Lemma lem4477726 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term462 A K k s t) = (term429 A K k s t).
Proof. exact (MK_COMB (@lem4477726 A K) (@lem4477725 A K k s t)). Qed.
Lemma lem4477728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term463 A K k s t) = (term430 A K k s t).
Proof. exact (MK_COMB (@lem4477728) (@lem4477727 A K k s t)). Qed.
Lemma lem4477730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term464 A K k s t x) = (term454 A K k s t x).
Proof. exact (eq_refl (term464 A K k s t x)). Qed.
Lemma lem4477731 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term465 A K k s t) = (term455 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477730 A K k s t x)). Qed.
Lemma lem4477732 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477733 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term466 A K k s t) = (term456 A K k s t).
Proof. exact (MK_COMB (@lem4477732 A K) (@lem4477731 A K k s t)). Qed.
Lemma lem4477734 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term458 A K k s t) = (term457 A K k s t).
Proof. exact (MK_COMB (@lem4477729 A K k s t) (@lem4477733 A K k s t)). Qed.
Lemma lem4477735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477736 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term467 A K k s t) = (term468 A K k s t).
Proof. exact (MK_COMB (@lem4477735) (@lem4477734 A K k s t)). Qed.
Lemma lem4477737 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term460 A K k s t x) = (term427 A K k s t x).
Proof. exact (eq_refl (term460 A K k s t x)). Qed.
Lemma lem4477738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477739 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term469 A K k s t x) = (term470 A K k s t x).
Proof. exact (MK_COMB (@lem4477738) (@lem4477737 A K k s t x)). Qed.
Lemma lem4477740 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term464 A K k s t x) = (term454 A K k s t x).
Proof. exact (eq_refl (term464 A K k s t x)). Qed.
Lemma lem4477741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term471 A K k s t x) = (term472 A K k s t x).
Proof. exact (MK_COMB (@lem4477739 A K k s t x) (@lem4477740 A K k s t x)). Qed.
Lemma lem4477742 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term473 A K k s t) = (term474 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477741 A K k s t x)). Qed.
Lemma lem4477743 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477744 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term459 A K k s t) = (term475 A K k s t).
Proof. exact (MK_COMB (@lem4477743 A K) (@lem4477742 A K k s t)). Qed.
Lemma lem4477745 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term458 A K k s t) = (term459 A K k s t)) = ((term457 A K k s t) = (term475 A K k s t)).
Proof. exact (MK_COMB (@lem4477736 A K k s t) (@lem4477744 A K k s t)). Qed.
Lemma lem4477746 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term457 A K k s t) = (term475 A K k s t).
Proof. exact (EQ_MP (@lem4477745 A K k s t) (@lem4477723 A K k s t)). Qed.
Lemma lem4477748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4477749 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term282 K P Q) = (term281 K P Q).
Proof. exact (@lem4477748 K P Q). Qed.
Lemma lem4477750 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term476 A K k s t x) = (term477 A K k s t x).
Proof. exact (@lem4477749 K (term426 A K k s t x) (term453 A K k s t x)). Qed.
Lemma lem4477751 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term478 A K k s t x i) = (term425 A K i k s t x).
Proof. exact (eq_refl (term478 A K k s t x i)). Qed.
Lemma lem4477752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term479 A K k s t x) = (term426 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477751 A K i k s t x)). Qed.
Lemma lem4477753 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477754 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term480 A K k s t x) = (term427 A K k s t x).
Proof. exact (MK_COMB (@lem4477753 K) (@lem4477752 A K k s t x)). Qed.
Lemma lem4477755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477756 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term481 A K k s t x) = (term470 A K k s t x).
Proof. exact (MK_COMB (@lem4477755) (@lem4477754 A K k s t x)). Qed.
Lemma lem4477757 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term482 A K k s t x i) = (term452 A K k s t x i).
Proof. exact (eq_refl (term482 A K k s t x i)). Qed.
Lemma lem4477758 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term483 A K k s t x) = (term453 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477757 A K k s t x i)). Qed.
Lemma lem4477759 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477760 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term484 A K k s t x) = (term454 A K k s t x).
Proof. exact (MK_COMB (@lem4477759 K) (@lem4477758 A K k s t x)). Qed.
Lemma lem4477761 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term476 A K k s t x) = (term472 A K k s t x).
Proof. exact (MK_COMB (@lem4477756 A K k s t x) (@lem4477760 A K k s t x)). Qed.
Lemma lem4477762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477763 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term485 A K k s t x) = (term486 A K k s t x).
Proof. exact (MK_COMB (@lem4477762) (@lem4477761 A K k s t x)). Qed.
Lemma lem4477764 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term478 A K k s t x i) = (term425 A K i k s t x).
Proof. exact (eq_refl (term478 A K k s t x i)). Qed.
Lemma lem4477765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477766 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term487 A K k s t x i) = (term488 A K i k s t x).
Proof. exact (MK_COMB (@lem4477765) (@lem4477764 A K i k s t x)). Qed.
Lemma lem4477767 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term482 A K k s t x i) = (term452 A K k s t x i).
Proof. exact (eq_refl (term482 A K k s t x i)). Qed.
Lemma lem4477768 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term489 A K k s t x i) = (term490 A K k s t x i).
Proof. exact (MK_COMB (@lem4477766 A K i k s t x) (@lem4477767 A K k s t x i)). Qed.
Lemma lem4477769 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term491 A K k s t x) = (term492 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477768 A K k s t x i)). Qed.
Lemma lem4477770 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477771 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term477 A K k s t x) = (term493 A K k s t x).
Proof. exact (MK_COMB (@lem4477770 K) (@lem4477769 A K k s t x)). Qed.
Lemma lem4477772 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : ((term476 A K k s t x) = (term477 A K k s t x)) = ((term472 A K k s t x) = (term493 A K k s t x)).
Proof. exact (MK_COMB (@lem4477763 A K k s t x) (@lem4477771 A K k s t x)). Qed.
Lemma lem4477773 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term472 A K k s t x) = (term493 A K k s t x).
Proof. exact (EQ_MP (@lem4477772 A K k s t x) (@lem4477750 A K k s t x)). Qed.
Lemma lem4477775 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4477776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term282 A P Q) = (term281 A P Q).
Proof. exact (@lem4477775 A P Q). Qed.
Lemma lem4477777 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term494 A K k s t x i) = (term495 A K k s t x i).
Proof. exact (@lem4477776 A (term424 A K i k s t x) (term451 A K k s t x i)). Qed.
Lemma lem4477778 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term496 A K i k s t x' x) = (term423 A K i x k s t x').
Proof. exact (eq_refl (term496 A K i k s t x' x)). Qed.
Lemma lem4477779 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term497 A K i k s t x) = (term424 A K i k s t x).
Proof. exact (fun_ext (fun x' : A => @lem4477778 A K i x' k s t x)). Qed.
Lemma lem4477780 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477781 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term498 A K i k s t x) = (term425 A K i k s t x).
Proof. exact (MK_COMB (@lem4477780 A) (@lem4477779 A K i k s t x)). Qed.
Lemma lem4477782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477783 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term499 A K i k s t x) = (term488 A K i k s t x).
Proof. exact (MK_COMB (@lem4477782) (@lem4477781 A K i k s t x)). Qed.
Lemma lem4477784 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term500 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term500 A K k s t x i x')). Qed.
Lemma lem4477785 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term501 A K k s t x i) = (term451 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4477784 A K k s t x i x')). Qed.
Lemma lem4477786 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477787 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term502 A K k s t x i) = (term452 A K k s t x i).
Proof. exact (MK_COMB (@lem4477786 A) (@lem4477785 A K k s t x i)). Qed.
Lemma lem4477788 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term494 A K k s t x i) = (term490 A K k s t x i).
Proof. exact (MK_COMB (@lem4477783 A K i k s t x) (@lem4477787 A K k s t x i)). Qed.
Lemma lem4477789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term503 A K k s t x i) = (term504 A K k s t x i).
Proof. exact (MK_COMB (@lem4477789) (@lem4477788 A K k s t x i)). Qed.
Lemma lem4477791 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term496 A K i k s t x' x) = (term423 A K i x k s t x').
Proof. exact (eq_refl (term496 A K i k s t x' x)). Qed.
Lemma lem4477792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477793 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term505 A K i k s t x' x) = (term506 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477792) (@lem4477791 A K i x k s t x')). Qed.
Lemma lem4477794 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term500 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term500 A K k s t x i x')). Qed.
Lemma lem4477795 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term507 A K k s t x i x') = (term508 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477793 A K i x' k s t x) (@lem4477794 A K k s t x i x')). Qed.
Lemma lem4477796 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term509 A K k s t x i) = (term510 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4477795 A K k s t x i x')). Qed.
Lemma lem4477797 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477798 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term495 A K k s t x i) = (term511 A K k s t x i).
Proof. exact (MK_COMB (@lem4477797 A) (@lem4477796 A K k s t x i)). Qed.
Lemma lem4477799 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : ((term494 A K k s t x i) = (term495 A K k s t x i)) = ((term490 A K k s t x i) = (term511 A K k s t x i)).
Proof. exact (MK_COMB (@lem4477790 A K k s t x i) (@lem4477798 A K k s t x i)). Qed.
Lemma lem4477800 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term490 A K k s t x i) = (term511 A K k s t x i).
Proof. exact (EQ_MP (@lem4477799 A K k s t x i) (@lem4477777 A K k s t x i)). Qed.
Lemma lem4477802 {A : Type'} (P : A -> Prop) (Q : Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4477803 {K : Type'} (P : K -> Prop) (Q : Prop) : (term512 K P Q) = (term513 K P Q).
Proof. exact (@lem4477802 K P Q). Qed.
Lemma lem4477804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term514 A K k s t x i x') = (term515 A K k s t x i x').
Proof. exact (@lem4477803 K (term422 A K i x' k s t x) (term449 A K k s t x i x')). Qed.
Lemma lem4477805 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term516 A K i x k s t x' i') = (term421 A K i x i' k s t x').
Proof. exact (eq_refl (term516 A K i x k s t x' i')). Qed.
Lemma lem4477806 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term517 A K i x k s t x') = (term422 A K i x k s t x').
Proof. exact (fun_ext (fun i' : K => @lem4477805 A K i x i' k s t x')). Qed.
Lemma lem4477807 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477808 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term518 A K i x k s t x') = (term423 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477807 K) (@lem4477806 A K i x k s t x')). Qed.
Lemma lem4477809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477810 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term519 A K i x k s t x') = (term506 A K i x k s t x').
Proof. exact (MK_COMB (@lem4477809) (@lem4477808 A K i x k s t x')). Qed.
Lemma lem4477811 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term449 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term449 A K k s t x i x')). Qed.
Lemma lem4477812 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term514 A K k s t x i x') = (term508 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477810 A K i x' k s t x) (@lem4477811 A K k s t x i x')). Qed.
Lemma lem4477813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477814 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term520 A K k s t x i x') = (term521 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477813) (@lem4477812 A K k s t x i x')). Qed.
Lemma lem4477815 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term516 A K i x k s t x' i') = (term421 A K i x i' k s t x').
Proof. exact (eq_refl (term516 A K i x k s t x' i')). Qed.
Lemma lem4477816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477817 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term522 A K i x k s t x' i') = (term523 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477816) (@lem4477815 A K i x i' k s t x')). Qed.
Lemma lem4477818 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term449 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term449 A K k s t x i x')). Qed.
Lemma lem4477819 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term524 A K i' k s t x i x') = (term525 A K i' k s t x i x').
Proof. exact (MK_COMB (@lem4477817 A K i x' i' k s t x) (@lem4477818 A K k s t x i x')). Qed.
Lemma lem4477820 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term526 A K k s t x i x') = (term527 A K k s t x i x').
Proof. exact (fun_ext (fun i' : K => @lem4477819 A K i' k s t x i x')). Qed.
Lemma lem4477821 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term515 A K k s t x i x') = (term528 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477821 K) (@lem4477820 A K k s t x i x')). Qed.
Lemma lem4477823 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term514 A K k s t x i x') = (term515 A K k s t x i x')) = ((term508 A K k s t x i x') = (term528 A K k s t x i x')).
Proof. exact (MK_COMB (@lem4477814 A K k s t x i x') (@lem4477822 A K k s t x i x')). Qed.
Lemma lem4477824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term508 A K k s t x i x') = (term528 A K k s t x i x').
Proof. exact (EQ_MP (@lem4477823 A K k s t x i x') (@lem4477804 A K k s t x i x')). Qed.
Lemma lem4477826 {A : Type'} (P : A -> Prop) (Q : Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4477827 {A : Type'} (P : A -> Prop) (Q : Prop) : (term512 A P Q) = (term513 A P Q).
Proof. exact (@lem4477826 A P Q). Qed.
Lemma lem4477828 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term529 A K i' k s t x i x') = (term530 A K i' k s t x i x').
Proof. exact (@lem4477827 A (term420 A K i x' i' k s t x) (term449 A K k s t x i x')). Qed.
Lemma lem4477829 {A K : Type'} (i : K) (x : A) (i' : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x'' : prod K A) : (term531 A K i x i' k s t x'' x') = (term418 A K i x i' x' k s t x'').
Proof. exact (eq_refl (term531 A K i x i' k s t x'' x')). Qed.
Lemma lem4477830 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term532 A K i x i' k s t x') = (term420 A K i x i' k s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4477829 A K i x i' x'' k s t x')). Qed.
Lemma lem4477831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477832 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term533 A K i x i' k s t x') = (term421 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477831 A) (@lem4477830 A K i x i' k s t x')). Qed.
Lemma lem4477833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477834 {A K : Type'} (i : K) (x : A) (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x' : prod K A) : (term534 A K i x i' k s t x') = (term523 A K i x i' k s t x').
Proof. exact (MK_COMB (@lem4477833) (@lem4477832 A K i x i' k s t x')). Qed.
Lemma lem4477835 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term449 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term449 A K k s t x i x')). Qed.
Lemma lem4477836 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term529 A K i' k s t x i x') = (term525 A K i' k s t x i x').
Proof. exact (MK_COMB (@lem4477834 A K i x' i' k s t x) (@lem4477835 A K k s t x i x')). Qed.
Lemma lem4477837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4477838 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term535 A K i' k s t x i x') = (term536 A K i' k s t x i x').
Proof. exact (MK_COMB (@lem4477837) (@lem4477836 A K i' k s t x i x')). Qed.
Lemma lem4477839 {A K : Type'} (i : K) (x : A) (i' : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x'' : prod K A) : (term531 A K i x i' k s t x'' x') = (term418 A K i x i' x' k s t x'').
Proof. exact (eq_refl (term531 A K i x i' k s t x'' x')). Qed.
Lemma lem4477840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4477841 {A K : Type'} (i : K) (x : A) (i' : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x'' : prod K A) : (term537 A K i x i' k s t x'' x') = (term538 A K i x i' x' k s t x'').
Proof. exact (MK_COMB (@lem4477840) (@lem4477839 A K i x i' x' k s t x'')). Qed.
Lemma lem4477842 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term449 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (eq_refl (term449 A K k s t x i x')). Qed.
Lemma lem4477843 {A K : Type'} (i' : K) (x' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x'' : A) : (term539 A K i' x' k s t x i x'') = (term540 A K i' x' k s t x i x'').
Proof. exact (MK_COMB (@lem4477841 A K i x'' i' x' k s t x) (@lem4477842 A K k s t x i x'')). Qed.
Lemma lem4477844 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term541 A K i' k s t x i x') = (term542 A K i' k s t x i x').
Proof. exact (fun_ext (fun x'' : A => @lem4477843 A K i' x'' k s t x i x')). Qed.
Lemma lem4477845 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477846 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term530 A K i' k s t x i x') = (term543 A K i' k s t x i x').
Proof. exact (MK_COMB (@lem4477845 A) (@lem4477844 A K i' k s t x i x')). Qed.
Lemma lem4477847 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : ((term529 A K i' k s t x i x') = (term530 A K i' k s t x i x')) = ((term525 A K i' k s t x i x') = (term543 A K i' k s t x i x')).
Proof. exact (MK_COMB (@lem4477838 A K i' k s t x i x') (@lem4477846 A K i' k s t x i x')). Qed.
Lemma lem4477848 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term525 A K i' k s t x i x') = (term543 A K i' k s t x i x').
Proof. exact (EQ_MP (@lem4477847 A K i' k s t x i x') (@lem4477828 A K i' k s t x i x')). Qed.
Lemma lem4477849 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term527 A K k s t x i x') = (term544 A K k s t x i x').
Proof. exact (fun_ext (fun i' : K => @lem4477848 A K i' k s t x i x')). Qed.
Lemma lem4477850 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477851 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term528 A K k s t x i x') = (term545 A K k s t x i x').
Proof. exact (MK_COMB (@lem4477850 K) (@lem4477849 A K k s t x i x')). Qed.
Lemma lem4477852 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term508 A K k s t x i x') = (term545 A K k s t x i x').
Proof. exact (TRANS (@lem4477824 A K k s t x i x') (@lem4477851 A K k s t x i x')). Qed.
Lemma lem4477853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term510 A K k s t x i) = (term546 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4477852 A K k s t x i x')). Qed.
Lemma lem4477854 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4477855 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term511 A K k s t x i) = (term547 A K k s t x i).
Proof. exact (MK_COMB (@lem4477854 A) (@lem4477853 A K k s t x i)). Qed.
Lemma lem4477856 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term490 A K k s t x i) = (term547 A K k s t x i).
Proof. exact (TRANS (@lem4477800 A K k s t x i) (@lem4477855 A K k s t x i)). Qed.
Lemma lem4477857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term492 A K k s t x) = (term548 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4477856 A K k s t x i)). Qed.
Lemma lem4477858 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4477859 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term493 A K k s t x) = (term549 A K k s t x).
Proof. exact (MK_COMB (@lem4477858 K) (@lem4477857 A K k s t x)). Qed.
Lemma lem4477860 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term472 A K k s t x) = (term549 A K k s t x).
Proof. exact (TRANS (@lem4477773 A K k s t x) (@lem4477859 A K k s t x)). Qed.
Lemma lem4477861 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term474 A K k s t) = (term550 A K k s t).
Proof. exact (fun_ext (fun x : prod K A => @lem4477860 A K k s t x)). Qed.
Lemma lem4477862 {A K : Type'} : (@ex (prod K A)) = (@ex (prod K A)).
Proof. exact (eq_refl (@ex (prod K A))). Qed.
Lemma lem4477863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term475 A K k s t) = (term551 A K k s t).
Proof. exact (MK_COMB (@lem4477862 A K) (@lem4477861 A K k s t)). Qed.
Lemma lem4477864 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term457 A K k s t) = (term551 A K k s t).
Proof. exact (TRANS (@lem4477746 A K k s t) (@lem4477863 A K k s t)). Qed.
Lemma lem4477865 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K k s t) = (term551 A K k s t).
Proof. exact (TRANS (@lem4477719 A K k s t) (@lem4477864 A K k s t)). Qed.
Lemma lem4477866 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term551 A K k s t).
Proof. exact (TRANS (@lem4477045 A K k s t) (@lem4477865 A K k s t)). Qed.
Lemma lem4477867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term152 A K k s t) = (term551 A K k s t).
Proof. exact (TRANS (@lem4477018 A K k s t) (@lem4477866 A K k s t)). Qed.
Lemma lem4477868 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term551 A K k s t.
Proof. exact (EQ_MP (@lem4477867 A K k s t) (@lem4476832 A K k s t h1)). Qed.
Lemma lem4478484 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term552 A K x a y b) = (term553 A K x a y b).
Proof. exact (@lem17045 (x = a) (y = b)). Qed.
Lemma lem4478490 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term554 A K x a y b) = (term554 A K x a y b).
Proof. exact (eq_refl (term554 A K x a y b)). Qed.
Lemma lem4478492 {A K : Type'} (x : K) (y : A) (a : K) (b : A) : (term555 A K x y a b) = (term555 A K x y a b).
Proof. exact (eq_refl (term555 A K x y a b)). Qed.
Lemma lem4478493 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term556 A K x a y b) = (term557 A K x a y b).
Proof. exact (MK_COMB (@lem4478492 A K x y a b) (@lem4478484 A K x a y b)). Qed.
Lemma lem4478494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478495 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term558 A K x a y b) = (term559 A K x a y b).
Proof. exact (MK_COMB (@lem4478494) (@lem4478493 A K x a y b)). Qed.
Lemma lem4478496 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term560 A K x a y b) = (term561 A K x a y b).
Proof. exact (MK_COMB (@lem4478495 A K x a y b) (@lem4478490 A K x a y b)). Qed.
Lemma lem4478497 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)) = (term560 A K x a y b).
Proof. exact (@lem17784 ((@pair K A x y) = (@pair K A a b)) (term190 A K x a y b)). Qed.
Lemma lem4478498 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (((@pair K A x y) = (@pair K A a b)) = (term190 A K x a y b)) = (term561 A K x a y b).
Proof. exact (TRANS (@lem4478497 A K x a y b) (@lem4478496 A K x a y b)). Qed.
Lemma lem4478499 {A K : Type'} (x : K) (a : K) (y : A) : (term191 A K x a y) = (term562 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4478498 A K x a y b)). Qed.
Lemma lem4478500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478501 {A K : Type'} (x : K) (a : K) (y : A) : (term192 A K x a y) = (term563 A K x a y).
Proof. exact (MK_COMB (@lem4478500 A) (@lem4478499 A K x a y)). Qed.
Lemma lem4478502 {A K : Type'} (x : K) (y : A) : (term193 A K x y) = (term564 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4478501 A K x a y)). Qed.
Lemma lem4478503 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478504 {A K : Type'} (x : K) (y : A) : (term194 A K x y) = (term565 A K x y).
Proof. exact (MK_COMB (@lem4478503 K) (@lem4478502 A K x y)). Qed.
Lemma lem4478505 {A K : Type'} (x : K) : (term195 A K x) = (term566 A K x).
Proof. exact (fun_ext (fun y : A => @lem4478504 A K x y)). Qed.
Lemma lem4478506 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478507 {A K : Type'} (x : K) : (term196 A K x) = (term567 A K x).
Proof. exact (MK_COMB (@lem4478506 A) (@lem4478505 A K x)). Qed.
Lemma lem4478508 {A K : Type'} : (term197 A K) = (term568 A K).
Proof. exact (fun_ext (fun x : K => @lem4478507 A K x)). Qed.
Lemma lem4478509 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478510 {A K : Type'} : (term153 A K) = (term569 A K).
Proof. exact (MK_COMB (@lem4478509 K) (@lem4478508 A K)). Qed.
Lemma lem4478524 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4478525 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (@lem4478524 A P Q). Qed.
Lemma lem4478526 {A K : Type'} (x : K) (a : K) (y : A) : (term572 A K x a y) = (term573 A K x a y).
Proof. exact (@lem4478525 A (term574 A K x a y) (term575 A K x a y)). Qed.
Lemma lem4478527 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term576 A K x a y b) = (term557 A K x a y b).
Proof. exact (eq_refl (term576 A K x a y b)). Qed.
Lemma lem4478528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478529 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term577 A K x a y b) = (term559 A K x a y b).
Proof. exact (MK_COMB (@lem4478528) (@lem4478527 A K x a y b)). Qed.
Lemma lem4478530 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term578 A K x a y b) = (term554 A K x a y b).
Proof. exact (eq_refl (term578 A K x a y b)). Qed.
Lemma lem4478531 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term579 A K x a y b) = (term561 A K x a y b).
Proof. exact (MK_COMB (@lem4478529 A K x a y b) (@lem4478530 A K x a y b)). Qed.
Lemma lem4478532 {A K : Type'} (x : K) (a : K) (y : A) : (term580 A K x a y) = (term562 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4478531 A K x a y b)). Qed.
Lemma lem4478533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478534 {A K : Type'} (x : K) (a : K) (y : A) : (term572 A K x a y) = (term563 A K x a y).
Proof. exact (MK_COMB (@lem4478533 A) (@lem4478532 A K x a y)). Qed.
Lemma lem4478535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4478536 {A K : Type'} (x : K) (a : K) (y : A) : (term581 A K x a y) = (term582 A K x a y).
Proof. exact (MK_COMB (@lem4478535) (@lem4478534 A K x a y)). Qed.
Lemma lem4478537 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term576 A K x a y b) = (term557 A K x a y b).
Proof. exact (eq_refl (term576 A K x a y b)). Qed.
Lemma lem4478538 {A K : Type'} (x : K) (a : K) (y : A) : (term583 A K x a y) = (term574 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4478537 A K x a y b)). Qed.
Lemma lem4478539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478540 {A K : Type'} (x : K) (a : K) (y : A) : (term584 A K x a y) = (term585 A K x a y).
Proof. exact (MK_COMB (@lem4478539 A) (@lem4478538 A K x a y)). Qed.
Lemma lem4478541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478542 {A K : Type'} (x : K) (a : K) (y : A) : (term586 A K x a y) = (term587 A K x a y).
Proof. exact (MK_COMB (@lem4478541) (@lem4478540 A K x a y)). Qed.
Lemma lem4478543 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term578 A K x a y b) = (term554 A K x a y b).
Proof. exact (eq_refl (term578 A K x a y b)). Qed.
Lemma lem4478544 {A K : Type'} (x : K) (a : K) (y : A) : (term588 A K x a y) = (term575 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4478543 A K x a y b)). Qed.
Lemma lem4478545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478546 {A K : Type'} (x : K) (a : K) (y : A) : (term589 A K x a y) = (term590 A K x a y).
Proof. exact (MK_COMB (@lem4478545 A) (@lem4478544 A K x a y)). Qed.
Lemma lem4478547 {A K : Type'} (x : K) (a : K) (y : A) : (term573 A K x a y) = (term591 A K x a y).
Proof. exact (MK_COMB (@lem4478542 A K x a y) (@lem4478546 A K x a y)). Qed.
Lemma lem4478548 {A K : Type'} (x : K) (a : K) (y : A) : ((term572 A K x a y) = (term573 A K x a y)) = ((term563 A K x a y) = (term591 A K x a y)).
Proof. exact (MK_COMB (@lem4478536 A K x a y) (@lem4478547 A K x a y)). Qed.
Lemma lem4478549 {A K : Type'} (x : K) (a : K) (y : A) : (term563 A K x a y) = (term591 A K x a y).
Proof. exact (EQ_MP (@lem4478548 A K x a y) (@lem4478526 A K x a y)). Qed.
Lemma lem4478646 {A K : Type'} (x : K) (y : A) : (term564 A K x y) = (term592 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4478549 A K x a y)). Qed.
Lemma lem4478647 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478648 {A K : Type'} (x : K) (y : A) : (term565 A K x y) = (term593 A K x y).
Proof. exact (MK_COMB (@lem4478647 K) (@lem4478646 A K x y)). Qed.
Lemma lem4478650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4478651 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term570 K P Q) = (term571 K P Q).
Proof. exact (@lem4478650 K P Q). Qed.
Lemma lem4478652 {A K : Type'} (x : K) (y : A) : (term594 A K x y) = (term595 A K x y).
Proof. exact (@lem4478651 K (term596 A K x y) (term597 A K x y)). Qed.
Lemma lem4478653 {A K : Type'} (x : K) (a : K) (y : A) : (term598 A K x y a) = (term585 A K x a y).
Proof. exact (eq_refl (term598 A K x y a)). Qed.
Lemma lem4478654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478655 {A K : Type'} (x : K) (a : K) (y : A) : (term599 A K x y a) = (term587 A K x a y).
Proof. exact (MK_COMB (@lem4478654) (@lem4478653 A K x a y)). Qed.
Lemma lem4478656 {A K : Type'} (x : K) (a : K) (y : A) : (term600 A K x y a) = (term590 A K x a y).
Proof. exact (eq_refl (term600 A K x y a)). Qed.
Lemma lem4478657 {A K : Type'} (x : K) (a : K) (y : A) : (term601 A K x y a) = (term591 A K x a y).
Proof. exact (MK_COMB (@lem4478655 A K x a y) (@lem4478656 A K x a y)). Qed.
Lemma lem4478658 {A K : Type'} (x : K) (y : A) : (term602 A K x y) = (term592 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4478657 A K x a y)). Qed.
Lemma lem4478659 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478660 {A K : Type'} (x : K) (y : A) : (term594 A K x y) = (term593 A K x y).
Proof. exact (MK_COMB (@lem4478659 K) (@lem4478658 A K x y)). Qed.
Lemma lem4478661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4478662 {A K : Type'} (x : K) (y : A) : (term603 A K x y) = (term604 A K x y).
Proof. exact (MK_COMB (@lem4478661) (@lem4478660 A K x y)). Qed.
Lemma lem4478663 {A K : Type'} (x : K) (a : K) (y : A) : (term598 A K x y a) = (term585 A K x a y).
Proof. exact (eq_refl (term598 A K x y a)). Qed.
Lemma lem4478664 {A K : Type'} (x : K) (y : A) : (term605 A K x y) = (term596 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4478663 A K x a y)). Qed.
Lemma lem4478665 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478666 {A K : Type'} (x : K) (y : A) : (term606 A K x y) = (term607 A K x y).
Proof. exact (MK_COMB (@lem4478665 K) (@lem4478664 A K x y)). Qed.
Lemma lem4478667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478668 {A K : Type'} (x : K) (y : A) : (term608 A K x y) = (term609 A K x y).
Proof. exact (MK_COMB (@lem4478667) (@lem4478666 A K x y)). Qed.
Lemma lem4478669 {A K : Type'} (x : K) (a : K) (y : A) : (term600 A K x y a) = (term590 A K x a y).
Proof. exact (eq_refl (term600 A K x y a)). Qed.
Lemma lem4478670 {A K : Type'} (x : K) (y : A) : (term610 A K x y) = (term597 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4478669 A K x a y)). Qed.
Lemma lem4478671 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478672 {A K : Type'} (x : K) (y : A) : (term611 A K x y) = (term612 A K x y).
Proof. exact (MK_COMB (@lem4478671 K) (@lem4478670 A K x y)). Qed.
Lemma lem4478673 {A K : Type'} (x : K) (y : A) : (term595 A K x y) = (term613 A K x y).
Proof. exact (MK_COMB (@lem4478668 A K x y) (@lem4478672 A K x y)). Qed.
Lemma lem4478674 {A K : Type'} (x : K) (y : A) : ((term594 A K x y) = (term595 A K x y)) = ((term593 A K x y) = (term613 A K x y)).
Proof. exact (MK_COMB (@lem4478662 A K x y) (@lem4478673 A K x y)). Qed.
Lemma lem4478675 {A K : Type'} (x : K) (y : A) : (term593 A K x y) = (term613 A K x y).
Proof. exact (EQ_MP (@lem4478674 A K x y) (@lem4478652 A K x y)). Qed.
Lemma lem4478780 {A K : Type'} (x : K) (y : A) : (term565 A K x y) = (term613 A K x y).
Proof. exact (TRANS (@lem4478648 A K x y) (@lem4478675 A K x y)). Qed.
Lemma lem4478781 {A K : Type'} (x : K) : (term566 A K x) = (term614 A K x).
Proof. exact (fun_ext (fun y : A => @lem4478780 A K x y)). Qed.
Lemma lem4478782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478783 {A K : Type'} (x : K) : (term567 A K x) = (term615 A K x).
Proof. exact (MK_COMB (@lem4478782 A) (@lem4478781 A K x)). Qed.
Lemma lem4478785 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4478786 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (@lem4478785 A P Q). Qed.
Lemma lem4478787 {A K : Type'} (x : K) : (term616 A K x) = (term617 A K x).
Proof. exact (@lem4478786 A (term618 A K x) (term619 A K x)). Qed.
Lemma lem4478788 {A K : Type'} (x : K) (y : A) : (term620 A K x y) = (term607 A K x y).
Proof. exact (eq_refl (term620 A K x y)). Qed.
Lemma lem4478789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478790 {A K : Type'} (x : K) (y : A) : (term621 A K x y) = (term609 A K x y).
Proof. exact (MK_COMB (@lem4478789) (@lem4478788 A K x y)). Qed.
Lemma lem4478791 {A K : Type'} (x : K) (y : A) : (term622 A K x y) = (term612 A K x y).
Proof. exact (eq_refl (term622 A K x y)). Qed.
Lemma lem4478792 {A K : Type'} (x : K) (y : A) : (term623 A K x y) = (term613 A K x y).
Proof. exact (MK_COMB (@lem4478790 A K x y) (@lem4478791 A K x y)). Qed.
Lemma lem4478793 {A K : Type'} (x : K) : (term624 A K x) = (term614 A K x).
Proof. exact (fun_ext (fun y : A => @lem4478792 A K x y)). Qed.
Lemma lem4478794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478795 {A K : Type'} (x : K) : (term616 A K x) = (term615 A K x).
Proof. exact (MK_COMB (@lem4478794 A) (@lem4478793 A K x)). Qed.
Lemma lem4478796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4478797 {A K : Type'} (x : K) : (term625 A K x) = (term626 A K x).
Proof. exact (MK_COMB (@lem4478796) (@lem4478795 A K x)). Qed.
Lemma lem4478798 {A K : Type'} (x : K) (y : A) : (term620 A K x y) = (term607 A K x y).
Proof. exact (eq_refl (term620 A K x y)). Qed.
Lemma lem4478799 {A K : Type'} (x : K) : (term627 A K x) = (term618 A K x).
Proof. exact (fun_ext (fun y : A => @lem4478798 A K x y)). Qed.
Lemma lem4478800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478801 {A K : Type'} (x : K) : (term628 A K x) = (term629 A K x).
Proof. exact (MK_COMB (@lem4478800 A) (@lem4478799 A K x)). Qed.
Lemma lem4478802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478803 {A K : Type'} (x : K) : (term630 A K x) = (term631 A K x).
Proof. exact (MK_COMB (@lem4478802) (@lem4478801 A K x)). Qed.
Lemma lem4478804 {A K : Type'} (x : K) (y : A) : (term622 A K x y) = (term612 A K x y).
Proof. exact (eq_refl (term622 A K x y)). Qed.
Lemma lem4478805 {A K : Type'} (x : K) : (term632 A K x) = (term619 A K x).
Proof. exact (fun_ext (fun y : A => @lem4478804 A K x y)). Qed.
Lemma lem4478806 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4478807 {A K : Type'} (x : K) : (term633 A K x) = (term634 A K x).
Proof. exact (MK_COMB (@lem4478806 A) (@lem4478805 A K x)). Qed.
Lemma lem4478808 {A K : Type'} (x : K) : (term617 A K x) = (term635 A K x).
Proof. exact (MK_COMB (@lem4478803 A K x) (@lem4478807 A K x)). Qed.
Lemma lem4478809 {A K : Type'} (x : K) : ((term616 A K x) = (term617 A K x)) = ((term615 A K x) = (term635 A K x)).
Proof. exact (MK_COMB (@lem4478797 A K x) (@lem4478808 A K x)). Qed.
Lemma lem4478810 {A K : Type'} (x : K) : (term615 A K x) = (term635 A K x).
Proof. exact (EQ_MP (@lem4478809 A K x) (@lem4478787 A K x)). Qed.
Lemma lem4478923 {A K : Type'} (x : K) : (term567 A K x) = (term635 A K x).
Proof. exact (TRANS (@lem4478783 A K x) (@lem4478810 A K x)). Qed.
Lemma lem4478924 {A K : Type'} : (term568 A K) = (term636 A K).
Proof. exact (fun_ext (fun x : K => @lem4478923 A K x)). Qed.
Lemma lem4478925 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478926 {A K : Type'} : (term569 A K) = (term637 A K).
Proof. exact (MK_COMB (@lem4478925 K) (@lem4478924 A K)). Qed.
Lemma lem4478928 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4478929 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term570 K P Q) = (term571 K P Q).
Proof. exact (@lem4478928 K P Q). Qed.
Lemma lem4478930 {A K : Type'} : (term638 A K) = (term639 A K).
Proof. exact (@lem4478929 K (term640 A K) (term641 A K)). Qed.
Lemma lem4478931 {A K : Type'} (x : K) : (term642 A K x) = (term629 A K x).
Proof. exact (eq_refl (term642 A K x)). Qed.
Lemma lem4478932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478933 {A K : Type'} (x : K) : (term643 A K x) = (term631 A K x).
Proof. exact (MK_COMB (@lem4478932) (@lem4478931 A K x)). Qed.
Lemma lem4478934 {A K : Type'} (x : K) : (term644 A K x) = (term634 A K x).
Proof. exact (eq_refl (term644 A K x)). Qed.
Lemma lem4478935 {A K : Type'} (x : K) : (term645 A K x) = (term635 A K x).
Proof. exact (MK_COMB (@lem4478933 A K x) (@lem4478934 A K x)). Qed.
Lemma lem4478936 {A K : Type'} : (term646 A K) = (term636 A K).
Proof. exact (fun_ext (fun x : K => @lem4478935 A K x)). Qed.
Lemma lem4478937 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478938 {A K : Type'} : (term638 A K) = (term637 A K).
Proof. exact (MK_COMB (@lem4478937 K) (@lem4478936 A K)). Qed.
Lemma lem4478939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4478940 {A K : Type'} : (term647 A K) = (term648 A K).
Proof. exact (MK_COMB (@lem4478939) (@lem4478938 A K)). Qed.
Lemma lem4478941 {A K : Type'} (x : K) : (term642 A K x) = (term629 A K x).
Proof. exact (eq_refl (term642 A K x)). Qed.
Lemma lem4478942 {A K : Type'} : (term649 A K) = (term640 A K).
Proof. exact (fun_ext (fun x : K => @lem4478941 A K x)). Qed.
Lemma lem4478943 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478944 {A K : Type'} : (term650 A K) = (term651 A K).
Proof. exact (MK_COMB (@lem4478943 K) (@lem4478942 A K)). Qed.
Lemma lem4478945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4478946 {A K : Type'} : (term652 A K) = (term653 A K).
Proof. exact (MK_COMB (@lem4478945) (@lem4478944 A K)). Qed.
Lemma lem4478947 {A K : Type'} (x : K) : (term644 A K x) = (term634 A K x).
Proof. exact (eq_refl (term644 A K x)). Qed.
Lemma lem4478948 {A K : Type'} : (term654 A K) = (term641 A K).
Proof. exact (fun_ext (fun x : K => @lem4478947 A K x)). Qed.
Lemma lem4478949 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4478950 {A K : Type'} : (term655 A K) = (term656 A K).
Proof. exact (MK_COMB (@lem4478949 K) (@lem4478948 A K)). Qed.
Lemma lem4478951 {A K : Type'} : (term639 A K) = (term657 A K).
Proof. exact (MK_COMB (@lem4478946 A K) (@lem4478950 A K)). Qed.
Lemma lem4478952 {A K : Type'} : ((term638 A K) = (term639 A K)) = ((term637 A K) = (term657 A K)).
Proof. exact (MK_COMB (@lem4478940 A K) (@lem4478951 A K)). Qed.
Lemma lem4478953 {A K : Type'} : (term637 A K) = (term657 A K).
Proof. exact (EQ_MP (@lem4478952 A K) (@lem4478930 A K)). Qed.
Lemma lem4479076 {A K : Type'} : (term569 A K) = (term657 A K).
Proof. exact (TRANS (@lem4478926 A K) (@lem4478953 A K)). Qed.
Lemma lem4479077 {A K : Type'} : (term153 A K) = (term657 A K).
Proof. exact (TRANS (@lem4478510 A K) (@lem4479076 A K)). Qed.
Lemma lem4479078 {A K : Type'} (h1 : term153 A K) : term657 A K.
Proof. exact (EQ_MP (@lem4479077 A K) (@lem4476834 A K h1)). Qed.
Lemma lem4479684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term549 A K k s t x) : term549 A K k s t x.
Proof. exact (h1). Qed.
Lemma lem4479685 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (h1 : term547 A K k s t x i) : term547 A K k s t x i.
Proof. exact (h1). Qed.
Lemma lem4479686 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term545 A K k s t x i x') : term545 A K k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4479687 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term543 A K i' k s t x i x') : term543 A K i' k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4479688 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term540 A K i' x'' k s t x i x') : term540 A K i' x'' k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4479811 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term554 A K x a y b) = (term554 A K x a y b).
Proof. exact (eq_refl (term554 A K x a y b)). Qed.
Lemma lem4479812 {A K : Type'} (x : K) (a : K) (y : A) : (term575 A K x a y) = (term575 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4479811 A K x a y b)). Qed.
Lemma lem4479813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4479814 {A K : Type'} (x : K) (a : K) (y : A) : (term590 A K x a y) = (term590 A K x a y).
Proof. exact (MK_COMB (@lem4479813 A) (@lem4479812 A K x a y)). Qed.
Lemma lem4479815 {A K : Type'} (x : K) (y : A) : (term597 A K x y) = (term597 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4479814 A K x a y)). Qed.
Lemma lem4479816 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4479817 {A K : Type'} (x : K) (y : A) : (term612 A K x y) = (term612 A K x y).
Proof. exact (MK_COMB (@lem4479816 K) (@lem4479815 A K x y)). Qed.
Lemma lem4479818 {A K : Type'} (x : K) : (term619 A K x) = (term619 A K x).
Proof. exact (fun_ext (fun y : A => @lem4479817 A K x y)). Qed.
Lemma lem4479819 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4479820 {A K : Type'} (x : K) : (term634 A K x) = (term634 A K x).
Proof. exact (MK_COMB (@lem4479819 A) (@lem4479818 A K x)). Qed.
Lemma lem4479821 {A K : Type'} : (term641 A K) = (term641 A K).
Proof. exact (fun_ext (fun x : K => @lem4479820 A K x)). Qed.
Lemma lem4479822 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4479823 {A K : Type'} : (term656 A K) = (term656 A K).
Proof. exact (MK_COMB (@lem4479822 K) (@lem4479821 A K)). Qed.
Lemma lem4479856 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term557 A K x a y b) = (term557 A K x a y b).
Proof. exact (eq_refl (term557 A K x a y b)). Qed.
Lemma lem4479857 {A K : Type'} (x : K) (a : K) (y : A) : (term574 A K x a y) = (term574 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4479856 A K x a y b)). Qed.
Lemma lem4479858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4479859 {A K : Type'} (x : K) (a : K) (y : A) : (term585 A K x a y) = (term585 A K x a y).
Proof. exact (MK_COMB (@lem4479858 A) (@lem4479857 A K x a y)). Qed.
Lemma lem4479860 {A K : Type'} (x : K) (y : A) : (term596 A K x y) = (term596 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4479859 A K x a y)). Qed.
Lemma lem4479861 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4479862 {A K : Type'} (x : K) (y : A) : (term607 A K x y) = (term607 A K x y).
Proof. exact (MK_COMB (@lem4479861 K) (@lem4479860 A K x y)). Qed.
Lemma lem4479863 {A K : Type'} (x : K) : (term618 A K x) = (term618 A K x).
Proof. exact (fun_ext (fun y : A => @lem4479862 A K x y)). Qed.
Lemma lem4479864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4479865 {A K : Type'} (x : K) : (term629 A K x) = (term629 A K x).
Proof. exact (MK_COMB (@lem4479864 A) (@lem4479863 A K x)). Qed.
Lemma lem4479866 {A K : Type'} : (term640 A K) = (term640 A K).
Proof. exact (fun_ext (fun x : K => @lem4479865 A K x)). Qed.
Lemma lem4479867 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4479868 {A K : Type'} : (term651 A K) = (term651 A K).
Proof. exact (MK_COMB (@lem4479867 K) (@lem4479866 A K)). Qed.
Lemma lem4479869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4479870 {A K : Type'} : (term653 A K) = (term653 A K).
Proof. exact (MK_COMB (@lem4479869) (@lem4479868 A K)). Qed.
Lemma lem4479871 {A K : Type'} : (term657 A K) = (term657 A K).
Proof. exact (MK_COMB (@lem4479870 A K) (@lem4479823 A K)). Qed.
Lemma lem4479872 {A K : Type'} (h1 : term153 A K) : term657 A K.
Proof. exact (EQ_MP (@lem4479871 A K) (@lem4479078 A K h1)). Qed.
Lemma lem4480001 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term139 A K k s t x i x') = (term139 A K k s t x i x').
Proof. exact (eq_refl (term139 A K k s t x i x')). Qed.
Lemma lem4480034 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (eq_refl (term213 A K k t x i x')). Qed.
Lemma lem4480035 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term222 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4480034 A K k t x i x')). Qed.
Lemma lem4480036 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480037 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term223 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4480036 A) (@lem4480035 A K k t x i)). Qed.
Lemma lem4480038 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term229 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4480037 A K k t x i)). Qed.
Lemma lem4480039 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480040 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term230 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4480039 K) (@lem4480038 A K k t x)). Qed.
Lemma lem4480073 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (eq_refl (term213 A K k s x i x')). Qed.
Lemma lem4480074 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term222 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4480073 A K k s x i x')). Qed.
Lemma lem4480075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term223 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4480075 A) (@lem4480074 A K k s x i)). Qed.
Lemma lem4480077 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term229 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4480076 A K k s x i)). Qed.
Lemma lem4480078 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480079 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term230 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4480078 K) (@lem4480077 A K k s x)). Qed.
Lemma lem4480080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4480081 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term232 A K k s x) = (term232 A K k s x).
Proof. exact (MK_COMB (@lem4480080) (@lem4480079 A K k s x)). Qed.
Lemma lem4480082 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term234 A K s k t x) = (term234 A K s k t x).
Proof. exact (MK_COMB (@lem4480081 A K k s x) (@lem4480040 A K k t x)). Qed.
Lemma lem4480083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4480084 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term262 A K s k t x) = (term262 A K s k t x).
Proof. exact (MK_COMB (@lem4480083) (@lem4480082 A K s k t x)). Qed.
Lemma lem4480085 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term449 A K k s t x i x') = (term449 A K k s t x i x').
Proof. exact (MK_COMB (@lem4480084 A K s k t x) (@lem4480001 A K k s t x i x')). Qed.
Lemma lem4480130 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (eq_refl (term245 A K k s t x i x')). Qed.
Lemma lem4480131 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term252 A K k s t x i) = (term252 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4480130 A K k s t x i x')). Qed.
Lemma lem4480132 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480133 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term253 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (MK_COMB (@lem4480132 A) (@lem4480131 A K k s t x i)). Qed.
Lemma lem4480134 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term259 A K k s t x) = (term259 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4480133 A K k s t x i)). Qed.
Lemma lem4480135 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480136 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (MK_COMB (@lem4480135 K) (@lem4480134 A K k s t x)). Qed.
Lemma lem4480195 {A K : Type'} (s : type1470 A K) (i : K) (x' : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i' : K) (x'' : A) : (term416 A K s i x' k t x i' x'') = (term416 A K s i x' k t x i' x'').
Proof. exact (eq_refl (term416 A K s i x' k t x i' x'')). Qed.
Lemma lem4480196 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term418 A K i x' i' x'' k s t x) = (term418 A K i x' i' x'' k s t x).
Proof. exact (MK_COMB (@lem4480195 A K s i x' k t x i' x'') (@lem4480136 A K k s t x)). Qed.
Lemma lem4480197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4480198 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term538 A K i x' i' x'' k s t x) = (term538 A K i x' i' x'' k s t x).
Proof. exact (MK_COMB (@lem4480197) (@lem4480196 A K i x' i' x'' k s t x)). Qed.
Lemma lem4480199 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term540 A K i' x'' k s t x i x') = (term540 A K i' x'' k s t x i x').
Proof. exact (MK_COMB (@lem4480198 A K i x' i' x'' k s t x) (@lem4480085 A K k s t x i x')). Qed.
Lemma lem4480200 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term540 A K i' x'' k s t x i x') : term540 A K i' x'' k s t x i x'.
Proof. exact (EQ_MP (@lem4480199 A K i' x'' k s t x i x') (@lem4479688 A K i' x'' k s t x i x' h1)). Qed.
Lemma lem4480203 {A K : Type'} (h1 : term153 A K) : term656 A K.
Proof. exact (proj2 (@lem4479872 A K h1)). Qed.
Lemma lem4480207 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term418 A K i x' i' x'' k s t x.
Proof. exact (h1). Qed.
Lemma lem4480208 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term449 A K k s t x i x'.
Proof. exact (h1). Qed.
Lemma lem4480209 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term260 A K k s t x.
Proof. exact (proj2 (@lem4480207 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480210 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term350 A K s i x' k t x i' x''.
Proof. exact (proj1 (@lem4480207 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480211 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term72 A K k t x i' x''.
Proof. exact (proj2 (@lem4480210 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480212 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term72 A K k s x i x'.
Proof. exact (proj1 (@lem4480210 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480214 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term56 A K k x'' t i'.
Proof. exact (proj1 (@lem4480211 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480218 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term56 A K k x' s i.
Proof. exact (proj1 (@lem4480212 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480221 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term139 A K k s t x i x'.
Proof. exact (proj2 (@lem4480208 A K k s t x i x' h1)). Qed.
Lemma lem4480222 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term234 A K s k t x.
Proof. exact (proj1 (@lem4480208 A K k s t x i x' h1)). Qed.
Lemma lem4480224 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term99 A K k s x' t i.
Proof. exact (proj1 (@lem4480221 A K k s t x i x' h1)). Qed.
Lemma lem4480225 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term96 A K s x' t i.
Proof. exact (proj2 (@lem4480224 A K k s t x i x' h1)). Qed.
Lemma lem4480229 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term230 A K k s x.
Proof. exact (h1). Qed.
Lemma lem4480230 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term230 A K k t x.
Proof. exact (h1). Qed.
Lemma lem4480336 {A K : Type'} (x : K) (a : K) (y : A) (b : A) : (term554 A K x a y b) = (term658 A K x a y b).
Proof. exact (@lem19490 (x = a) (term659 A K x y a b) (y = b)). Qed.
Lemma lem4480337 {A K : Type'} (x : K) (a : K) (y : A) : (term575 A K x a y) = (term660 A K x a y).
Proof. exact (fun_ext (fun b : A => @lem4480336 A K x a y b)). Qed.
Lemma lem4480338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480339 {A K : Type'} (x : K) (a : K) (y : A) : (term590 A K x a y) = (term661 A K x a y).
Proof. exact (MK_COMB (@lem4480338 A) (@lem4480337 A K x a y)). Qed.
Lemma lem4480340 {A K : Type'} (x : K) (y : A) : (term597 A K x y) = (term662 A K x y).
Proof. exact (fun_ext (fun a : K => @lem4480339 A K x a y)). Qed.
Lemma lem4480341 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480342 {A K : Type'} (x : K) (y : A) : (term612 A K x y) = (term663 A K x y).
Proof. exact (MK_COMB (@lem4480341 K) (@lem4480340 A K x y)). Qed.
Lemma lem4480343 {A K : Type'} (x : K) : (term619 A K x) = (term664 A K x).
Proof. exact (fun_ext (fun y : A => @lem4480342 A K x y)). Qed.
Lemma lem4480344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480345 {A K : Type'} (x : K) : (term634 A K x) = (term665 A K x).
Proof. exact (MK_COMB (@lem4480344 A) (@lem4480343 A K x)). Qed.
Lemma lem4480346 {A K : Type'} : (term641 A K) = (term666 A K).
Proof. exact (fun_ext (fun x : K => @lem4480345 A K x)). Qed.
Lemma lem4480347 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480349 {A K : Type'} : (term656 A K) = (term667 A K).
Proof. exact (MK_COMB (@lem4480347 K) (@lem4480346 A K)). Qed.
Lemma lem4480350 {A K : Type'} (h1 : term153 A K) : term667 A K.
Proof. exact (EQ_MP (@lem4480349 A K) (@lem4480203 A K h1)). Qed.
Lemma lem4480430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term245 A K k s t x i x') = (term245 A K k s t x i x').
Proof. exact (eq_refl (term245 A K k s t x i x')). Qed.
Lemma lem4480431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term252 A K k s t x i) = (term252 A K k s t x i).
Proof. exact (fun_ext (fun x' : A => @lem4480430 A K k s t x i x')). Qed.
Lemma lem4480432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) : (term253 A K k s t x i) = (term253 A K k s t x i).
Proof. exact (MK_COMB (@lem4480432 A) (@lem4480431 A K k s t x i)). Qed.
Lemma lem4480434 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term259 A K k s t x) = (term259 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4480433 A K k s t x i)). Qed.
Lemma lem4480435 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480437 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) : (term260 A K k s t x) = (term260 A K k s t x).
Proof. exact (MK_COMB (@lem4480435 K) (@lem4480434 A K k s t x)). Qed.
Lemma lem4480438 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term260 A K k s t x.
Proof. exact (EQ_MP (@lem4480437 A K k s t x) (@lem4480209 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4480672 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k s x i x') = (term213 A K k s x i x').
Proof. exact (eq_refl (term213 A K k s x i x')). Qed.
Lemma lem4480673 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term222 A K k s x i) = (term222 A K k s x i).
Proof. exact (fun_ext (fun x' : A => @lem4480672 A K k s x i x')). Qed.
Lemma lem4480674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480675 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (i : K) : (term223 A K k s x i) = (term223 A K k s x i).
Proof. exact (MK_COMB (@lem4480674 A) (@lem4480673 A K k s x i)). Qed.
Lemma lem4480676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term229 A K k s x) = (term229 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4480675 A K k s x i)). Qed.
Lemma lem4480677 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) : (term230 A K k s x) = (term230 A K k s x).
Proof. exact (MK_COMB (@lem4480677 K) (@lem4480676 A K k s x)). Qed.
Lemma lem4480680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term230 A K k s x.
Proof. exact (EQ_MP (@lem4480679 A K k s x) (@lem4480229 A K k s x h1)). Qed.
Lemma lem4480890 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) : (term213 A K k t x i x') = (term213 A K k t x i x').
Proof. exact (eq_refl (term213 A K k t x i x')). Qed.
Lemma lem4480891 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term222 A K k t x i) = (term222 A K k t x i).
Proof. exact (fun_ext (fun x' : A => @lem4480890 A K k t x i x')). Qed.
Lemma lem4480892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4480893 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (i : K) : (term223 A K k t x i) = (term223 A K k t x i).
Proof. exact (MK_COMB (@lem4480892 A) (@lem4480891 A K k t x i)). Qed.
Lemma lem4480894 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term229 A K k t x) = (term229 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4480893 A K k t x i)). Qed.
Lemma lem4480895 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4480897 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) : (term230 A K k t x) = (term230 A K k t x).
Proof. exact (MK_COMB (@lem4480895 K) (@lem4480894 A K k t x)). Qed.
Lemma lem4480898 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term230 A K k t x.
Proof. exact (EQ_MP (@lem4480897 A K k t x) (@lem4480230 A K k t x h1)). Qed.
Lemma lem4480935 {A K : Type'} (_51755 : K) (h1 : term153 A K) : term668 A K _51755.
Proof. exact (@lem4480350 A K h1 _51755). Qed.
Lemma lem4480936 {A K : Type'} (_51755 : K) : (term668 A K _51755) = (term665 A K _51755).
Proof. exact (eq_refl (term668 A K _51755)). Qed.
Lemma lem4480937 {A K : Type'} (_51755 : K) (h1 : term153 A K) : term665 A K _51755.
Proof. exact (EQ_MP (@lem4480936 A K _51755) (@lem4480935 A K _51755 h1)). Qed.
Lemma lem4480938 {A K : Type'} (_51755 : K) (_51756 : A) (h1 : term153 A K) : term669 A K _51755 _51756.
Proof. exact (@lem4480937 A K _51755 h1 _51756). Qed.
Lemma lem4480939 {A K : Type'} (_51755 : K) (_51756 : A) : (term669 A K _51755 _51756) = (term663 A K _51755 _51756).
Proof. exact (eq_refl (term669 A K _51755 _51756)). Qed.
Lemma lem4480940 {A K : Type'} (_51755 : K) (_51756 : A) (h1 : term153 A K) : term663 A K _51755 _51756.
Proof. exact (EQ_MP (@lem4480939 A K _51755 _51756) (@lem4480938 A K _51755 _51756 h1)). Qed.
Lemma lem4480941 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (h1 : term153 A K) : term670 A K _51755 _51756 _51757.
Proof. exact (@lem4480940 A K _51755 _51756 h1 _51757). Qed.
Lemma lem4480942 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) : (term670 A K _51755 _51756 _51757) = (term661 A K _51755 _51757 _51756).
Proof. exact (eq_refl (term670 A K _51755 _51756 _51757)). Qed.
Lemma lem4480943 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (h1 : term153 A K) : term661 A K _51755 _51757 _51756.
Proof. exact (EQ_MP (@lem4480942 A K _51755 _51757 _51756) (@lem4480941 A K _51755 _51756 _51757 h1)). Qed.
Lemma lem4480944 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) (h1 : term153 A K) : term671 A K _51755 _51757 _51756 _51758.
Proof. exact (@lem4480943 A K _51755 _51757 _51756 h1 _51758). Qed.
Lemma lem4480945 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) : (term671 A K _51755 _51757 _51756 _51758) = (term658 A K _51755 _51757 _51756 _51758).
Proof. exact (eq_refl (term671 A K _51755 _51757 _51756 _51758)). Qed.
Lemma lem4480946 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) (h1 : term153 A K) : term658 A K _51755 _51757 _51756 _51758.
Proof. exact (EQ_MP (@lem4480945 A K _51755 _51757 _51756 _51758) (@lem4480944 A K _51755 _51757 _51756 _51758 h1)). Qed.
Lemma lem4480971 {A K : Type'} (_51767 : K) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term672 A K k s t x _51767.
Proof. exact (@lem4480438 A K i x' i' x'' k s t x h1 _51767). Qed.
Lemma lem4480972 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) : (term672 A K k s t x _51767) = (term253 A K k s t x _51767).
Proof. exact (eq_refl (term672 A K k s t x _51767)). Qed.
Lemma lem4480973 {A K : Type'} (_51767 : K) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term253 A K k s t x _51767.
Proof. exact (EQ_MP (@lem4480972 A K k s t x _51767) (@lem4480971 A K _51767 i x' i' x'' k s t x h1)). Qed.
Lemma lem4480974 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term673 A K k s t x _51767 _51768.
Proof. exact (@lem4480973 A K _51767 i x' i' x'' k s t x h1 _51768). Qed.
Lemma lem4480975 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term673 A K k s t x _51767 _51768) = (term245 A K k s t x _51767 _51768).
Proof. exact (eq_refl (term673 A K k s t x _51767 _51768)). Qed.
Lemma lem4480976 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term245 A K k s t x _51767 _51768.
Proof. exact (EQ_MP (@lem4480975 A K k s t x _51767 _51768) (@lem4480974 A K _51767 _51768 i x' i' x'' k s t x h1)). Qed.
Lemma lem4481049 {A K : Type'} (_51793 : K) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term674 A K k s x _51793.
Proof. exact (@lem4480680 A K k s x h1 _51793). Qed.
Lemma lem4481050 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_51793 : K) : (term674 A K k s x _51793) = (term223 A K k s x _51793).
Proof. exact (eq_refl (term674 A K k s x _51793)). Qed.
Lemma lem4481051 {A K : Type'} (_51793 : K) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term223 A K k s x _51793.
Proof. exact (EQ_MP (@lem4481050 A K k s x _51793) (@lem4481049 A K _51793 k s x h1)). Qed.
Lemma lem4481052 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term675 A K k s x _51793 _51794.
Proof. exact (@lem4481051 A K _51793 k s x h1 _51794). Qed.
Lemma lem4481053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_51793 : K) (_51794 : A) : (term675 A K k s x _51793 _51794) = (term213 A K k s x _51793 _51794).
Proof. exact (eq_refl (term675 A K k s x _51793 _51794)). Qed.
Lemma lem4481054 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term213 A K k s x _51793 _51794.
Proof. exact (EQ_MP (@lem4481053 A K k s x _51793 _51794) (@lem4481052 A K _51793 _51794 k s x h1)). Qed.
Lemma lem4481127 {A K : Type'} (_51819 : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term674 A K k t x _51819.
Proof. exact (@lem4480898 A K k t x h1 _51819). Qed.
Lemma lem4481128 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_51819 : K) : (term674 A K k t x _51819) = (term223 A K k t x _51819).
Proof. exact (eq_refl (term674 A K k t x _51819)). Qed.
Lemma lem4481129 {A K : Type'} (_51819 : K) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term223 A K k t x _51819.
Proof. exact (EQ_MP (@lem4481128 A K k t x _51819) (@lem4481127 A K _51819 k t x h1)). Qed.
Lemma lem4481130 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term675 A K k t x _51819 _51820.
Proof. exact (@lem4481129 A K _51819 k t x h1 _51820). Qed.
Lemma lem4481131 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_51819 : K) (_51820 : A) : (term675 A K k t x _51819 _51820) = (term213 A K k t x _51819 _51820).
Proof. exact (eq_refl (term675 A K k t x _51819 _51820)). Qed.
Lemma lem4481132 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term213 A K k t x _51819 _51820.
Proof. exact (EQ_MP (@lem4481131 A K k t x _51819 _51820) (@lem4481130 A K _51819 _51820 k t x h1)). Qed.
Lemma lem4481184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term245 A K k s t x _51767 _51768) = (term676 A K k s t x _51767 _51768).
Proof. exact (@lem4475759 (term677 K _51767 k) (term237 A K s _51768 t _51767) (term209 A K x _51767 _51768)). Qed.
Lemma lem4481191 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term678 A K s t x _51767 _51768) = (term679 A K s t x _51767 _51768).
Proof. exact (@lem4475759 (term680 A K _51768 s _51767) (term680 A K _51768 t _51767) (term209 A K x _51767 _51768)). Qed.
Lemma lem4481192 {K : Type'} (_51767 : K) (k : K -> Prop) : (term238 K _51767 k) = (term238 K _51767 k).
Proof. exact (eq_refl (term238 K _51767 k)). Qed.
Lemma lem4481195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term676 A K k s t x _51767 _51768) = (term681 A K k s t x _51767 _51768).
Proof. exact (MK_COMB (@lem4481192 K _51767 k) (@lem4481191 A K s t x _51767 _51768)). Qed.
Lemma lem4481197 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term245 A K k s t x _51767 _51768) = (term681 A K k s t x _51767 _51768).
Proof. exact (TRANS (@lem4481184 A K k s t x _51767 _51768) (@lem4481195 A K k s t x _51767 _51768)). Qed.
Lemma lem4481198 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term681 A K k s t x _51767 _51768.
Proof. exact (EQ_MP (@lem4481197 A K k s t x _51767 _51768) (@lem4480976 A K _51767 _51768 i x' i' x'' k s t x h1)). Qed.
Lemma lem4481200 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : x = (@pair K A i' x'').
Proof. exact (proj2 (@lem4480211 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4481206 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : x = (@pair K A i x').
Proof. exact (proj2 (@lem4480212 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4481278 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4480221 A K k s t x i x' h1)). Qed.
Lemma lem4481295 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_51793 : K) (_51794 : A) : (term213 A K k s x _51793 _51794) = (term682 A K k s x _51793 _51794).
Proof. exact (@lem4475759 (term677 K _51793 k) (term680 A K _51794 s _51793) (term209 A K x _51793 _51794)). Qed.
Lemma lem4481296 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (x : prod K A) (h1 : term230 A K k s x) : term682 A K k s x _51793 _51794.
Proof. exact (EQ_MP (@lem4481295 A K k s x _51793 _51794) (@lem4481054 A K _51793 _51794 k s x h1)). Qed.
Lemma lem4481364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : x = (@pair K A i x').
Proof. exact (proj2 (@lem4480221 A K k s t x i x' h1)). Qed.
Lemma lem4481381 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_51819 : K) (_51820 : A) : (term213 A K k t x _51819 _51820) = (term682 A K k t x _51819 _51820).
Proof. exact (@lem4475759 (term677 K _51819 k) (term680 A K _51820 t _51819) (term209 A K x _51819 _51820)). Qed.
Lemma lem4481382 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (t : type1470 A K) (x : prod K A) (h1 : term230 A K k t x) : term682 A K k t x _51819 _51820.
Proof. exact (EQ_MP (@lem4481381 A K k t x _51819 _51820) (@lem4481132 A K _51819 _51820 k t x h1)). Qed.
Lemma lem4481475 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51767 : K) (_51768 : A) : (term683 A K k s t _51767 _51768) = (term683 A K k s t _51767 _51768).
Proof. exact (eq_refl (term683 A K k s t _51767 _51768)). Qed.
Lemma lem4481476 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (term684 A K k s t _51767 _51768 x) = (term685 A K k s t _51767 _51768 i x').
Proof. exact (MK_COMB (@lem4481475 A K k s t _51767 _51768) (@lem4481206 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4481477 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term685 A K k s t _51767 _51768 i x') = (term686 A K k s t i x' _51767 _51768).
Proof. exact (eq_refl (term685 A K k s t _51767 _51768 i x')). Qed.
Lemma lem4481478 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51767 : K) (_51768 : A) (x : prod K A) : (term687 A K k s t _51767 _51768 x) = (term687 A K k s t _51767 _51768 x).
Proof. exact (eq_refl (term687 A K k s t _51767 _51768 x)). Qed.
Lemma lem4481479 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : ((term684 A K k s t _51767 _51768 x) = (term685 A K k s t _51767 _51768 i x')) = ((term684 A K k s t _51767 _51768 x) = (term686 A K k s t i x' _51767 _51768)).
Proof. exact (MK_COMB (@lem4481478 A K k s t _51767 _51768 x) (@lem4481477 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4481480 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term684 A K k s t _51767 _51768 x) = (term681 A K k s t x _51767 _51768).
Proof. exact (eq_refl (term684 A K k s t _51767 _51768 x)). Qed.
Lemma lem4481481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4481482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (_51767 : K) (_51768 : A) : (term687 A K k s t _51767 _51768 x) = (term688 A K k s t x _51767 _51768).
Proof. exact (MK_COMB (@lem4481481) (@lem4481480 A K k s t x _51767 _51768)). Qed.
Lemma lem4481483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term686 A K k s t i x' _51767 _51768) = (term686 A K k s t i x' _51767 _51768).
Proof. exact (eq_refl (term686 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4481484 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : ((term684 A K k s t _51767 _51768 x) = (term686 A K k s t i x' _51767 _51768)) = ((term681 A K k s t x _51767 _51768) = (term686 A K k s t i x' _51767 _51768)).
Proof. exact (MK_COMB (@lem4481482 A K k s t x _51767 _51768) (@lem4481483 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4481485 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : ((term684 A K k s t _51767 _51768 x) = (term685 A K k s t _51767 _51768 i x')) = ((term681 A K k s t x _51767 _51768) = (term686 A K k s t i x' _51767 _51768)).
Proof. exact (TRANS (@lem4481479 A K x k s t i x' _51767 _51768) (@lem4481484 A K x k s t i x' _51767 _51768)). Qed.
Lemma lem4481486 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (term681 A K k s t x _51767 _51768) = (term686 A K k s t i x' _51767 _51768).
Proof. exact (EQ_MP (@lem4481485 A K x k s t i x' _51767 _51768) (@lem4481476 A K _51767 _51768 i x' i' x'' k s t x h1)). Qed.
Lemma lem4481487 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term686 A K k s t i x' _51767 _51768.
Proof. exact (EQ_MP (@lem4481486 A K _51767 _51768 i x' i' x'' k s t x h1) (@lem4481198 A K _51767 _51768 i x' i' x'' k s t x h1)). Qed.
Lemma lem4481488 {A K : Type'} (i' : K) (x'' : A) : (term689 A K i' x'') = (term689 A K i' x'').
Proof. exact (eq_refl (term689 A K i' x'')). Qed.
Lemma lem4481489 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (term690 A K i' x'' x) = (term691 A K i' x'' i x').
Proof. exact (MK_COMB (@lem4481488 A K i' x'') (@lem4481206 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4481490 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) : (term691 A K i' x'' i x') = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (eq_refl (term691 A K i' x'' i x')). Qed.
Lemma lem4481491 {A K : Type'} (i' : K) (x'' : A) (x : prod K A) : (term692 A K i' x'' x) = (term692 A K i' x'' x).
Proof. exact (eq_refl (term692 A K i' x'' x)). Qed.
Lemma lem4481492 {A K : Type'} (x : prod K A) (i : K) (x' : A) (i' : K) (x'' : A) : ((term690 A K i' x'' x) = (term691 A K i' x'' i x')) = ((term690 A K i' x'' x) = ((@pair K A i x') = (@pair K A i' x''))).
Proof. exact (MK_COMB (@lem4481491 A K i' x'' x) (@lem4481490 A K i x' i' x'')). Qed.
Lemma lem4481493 {A K : Type'} (x : prod K A) (i' : K) (x'' : A) : (term690 A K i' x'' x) = (x = (@pair K A i' x'')).
Proof. exact (eq_refl (term690 A K i' x'' x)). Qed.
Lemma lem4481494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4481495 {A K : Type'} (x : prod K A) (i' : K) (x'' : A) : (term692 A K i' x'' x) = (term693 A K x i' x'').
Proof. exact (MK_COMB (@lem4481494) (@lem4481493 A K x i' x'')). Qed.
Lemma lem4481496 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) : ((@pair K A i x') = (@pair K A i' x'')) = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (eq_refl ((@pair K A i x') = (@pair K A i' x''))). Qed.
Lemma lem4481497 {A K : Type'} (x : prod K A) (i : K) (x' : A) (i' : K) (x'' : A) : ((term690 A K i' x'' x) = ((@pair K A i x') = (@pair K A i' x''))) = ((x = (@pair K A i' x'')) = ((@pair K A i x') = (@pair K A i' x''))).
Proof. exact (MK_COMB (@lem4481495 A K x i' x'') (@lem4481496 A K i x' i' x'')). Qed.
Lemma lem4481498 {A K : Type'} (x : prod K A) (i : K) (x' : A) (i' : K) (x'' : A) : ((term690 A K i' x'' x) = (term691 A K i' x'' i x')) = ((x = (@pair K A i' x'')) = ((@pair K A i x') = (@pair K A i' x''))).
Proof. exact (TRANS (@lem4481492 A K x i x' i' x'') (@lem4481497 A K x i x' i' x'')). Qed.
Lemma lem4481499 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (x = (@pair K A i' x'')) = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (EQ_MP (@lem4481498 A K x i x' i' x'') (@lem4481489 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4481598 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) (h1 : term153 A K) : term694 A K _51756 _51758 _51755 _51757.
Proof. exact (proj1 (@lem4480946 A K _51755 _51757 _51756 _51758 h1)). Qed.
Lemma lem4481612 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) (h1 : term153 A K) : term695 A K _51755 _51757 _51756 _51758.
Proof. exact (proj2 (@lem4480946 A K _51755 _51757 _51756 _51758 h1)). Qed.
Lemma lem4481739 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51793 : K) (_51794 : A) : (term696 A K k s _51793 _51794) = (term696 A K k s _51793 _51794).
Proof. exact (eq_refl (term696 A K k s _51793 _51794)). Qed.
Lemma lem4481740 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : (term697 A K k s _51793 _51794 x) = (term698 A K k s _51793 _51794 i x').
Proof. exact (MK_COMB (@lem4481739 A K k s _51793 _51794) (@lem4481278 A K k s t x i x' h1)). Qed.
Lemma lem4481741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term698 A K k s _51793 _51794 i x') = (term699 A K k s i x' _51793 _51794).
Proof. exact (eq_refl (term698 A K k s _51793 _51794 i x')). Qed.
Lemma lem4481742 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51793 : K) (_51794 : A) (x : prod K A) : (term700 A K k s _51793 _51794 x) = (term700 A K k s _51793 _51794 x).
Proof. exact (eq_refl (term700 A K k s _51793 _51794 x)). Qed.
Lemma lem4481743 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : ((term697 A K k s _51793 _51794 x) = (term698 A K k s _51793 _51794 i x')) = ((term697 A K k s _51793 _51794 x) = (term699 A K k s i x' _51793 _51794)).
Proof. exact (MK_COMB (@lem4481742 A K k s _51793 _51794 x) (@lem4481741 A K k s i x' _51793 _51794)). Qed.
Lemma lem4481744 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_51793 : K) (_51794 : A) : (term697 A K k s _51793 _51794 x) = (term682 A K k s x _51793 _51794).
Proof. exact (eq_refl (term697 A K k s _51793 _51794 x)). Qed.
Lemma lem4481745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4481746 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : prod K A) (_51793 : K) (_51794 : A) : (term700 A K k s _51793 _51794 x) = (term701 A K k s x _51793 _51794).
Proof. exact (MK_COMB (@lem4481745) (@lem4481744 A K k s x _51793 _51794)). Qed.
Lemma lem4481747 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term699 A K k s i x' _51793 _51794) = (term699 A K k s i x' _51793 _51794).
Proof. exact (eq_refl (term699 A K k s i x' _51793 _51794)). Qed.
Lemma lem4481748 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : ((term697 A K k s _51793 _51794 x) = (term699 A K k s i x' _51793 _51794)) = ((term682 A K k s x _51793 _51794) = (term699 A K k s i x' _51793 _51794)).
Proof. exact (MK_COMB (@lem4481746 A K k s x _51793 _51794) (@lem4481747 A K k s i x' _51793 _51794)). Qed.
Lemma lem4481749 {A K : Type'} (x : prod K A) (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : ((term697 A K k s _51793 _51794 x) = (term698 A K k s _51793 _51794 i x')) = ((term682 A K k s x _51793 _51794) = (term699 A K k s i x' _51793 _51794)).
Proof. exact (TRANS (@lem4481743 A K x k s i x' _51793 _51794) (@lem4481748 A K x k s i x' _51793 _51794)). Qed.
Lemma lem4481750 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : (term682 A K k s x _51793 _51794) = (term699 A K k s i x' _51793 _51794).
Proof. exact (EQ_MP (@lem4481749 A K x k s i x' _51793 _51794) (@lem4481740 A K _51793 _51794 k s t x i x' h1)). Qed.
Lemma lem4481751 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : term699 A K k s i x' _51793 _51794.
Proof. exact (EQ_MP (@lem4481750 A K _51793 _51794 k s t x i x' h2) (@lem4481296 A K _51793 _51794 k s x h1)). Qed.
Lemma lem4481934 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51819 : K) (_51820 : A) : (term696 A K k t _51819 _51820) = (term696 A K k t _51819 _51820).
Proof. exact (eq_refl (term696 A K k t _51819 _51820)). Qed.
Lemma lem4481935 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : (term697 A K k t _51819 _51820 x) = (term698 A K k t _51819 _51820 i x').
Proof. exact (MK_COMB (@lem4481934 A K k t _51819 _51820) (@lem4481364 A K k s t x i x' h1)). Qed.
Lemma lem4481936 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term698 A K k t _51819 _51820 i x') = (term699 A K k t i x' _51819 _51820).
Proof. exact (eq_refl (term698 A K k t _51819 _51820 i x')). Qed.
Lemma lem4481937 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51819 : K) (_51820 : A) (x : prod K A) : (term700 A K k t _51819 _51820 x) = (term700 A K k t _51819 _51820 x).
Proof. exact (eq_refl (term700 A K k t _51819 _51820 x)). Qed.
Lemma lem4481938 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : ((term697 A K k t _51819 _51820 x) = (term698 A K k t _51819 _51820 i x')) = ((term697 A K k t _51819 _51820 x) = (term699 A K k t i x' _51819 _51820)).
Proof. exact (MK_COMB (@lem4481937 A K k t _51819 _51820 x) (@lem4481936 A K k t i x' _51819 _51820)). Qed.
Lemma lem4481939 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_51819 : K) (_51820 : A) : (term697 A K k t _51819 _51820 x) = (term682 A K k t x _51819 _51820).
Proof. exact (eq_refl (term697 A K k t _51819 _51820 x)). Qed.
Lemma lem4481940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4481941 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : prod K A) (_51819 : K) (_51820 : A) : (term700 A K k t _51819 _51820 x) = (term701 A K k t x _51819 _51820).
Proof. exact (MK_COMB (@lem4481940) (@lem4481939 A K k t x _51819 _51820)). Qed.
Lemma lem4481942 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term699 A K k t i x' _51819 _51820) = (term699 A K k t i x' _51819 _51820).
Proof. exact (eq_refl (term699 A K k t i x' _51819 _51820)). Qed.
Lemma lem4481943 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : ((term697 A K k t _51819 _51820 x) = (term699 A K k t i x' _51819 _51820)) = ((term682 A K k t x _51819 _51820) = (term699 A K k t i x' _51819 _51820)).
Proof. exact (MK_COMB (@lem4481941 A K k t x _51819 _51820) (@lem4481942 A K k t i x' _51819 _51820)). Qed.
Lemma lem4481944 {A K : Type'} (x : prod K A) (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : ((term697 A K k t _51819 _51820 x) = (term698 A K k t _51819 _51820 i x')) = ((term682 A K k t x _51819 _51820) = (term699 A K k t i x' _51819 _51820)).
Proof. exact (TRANS (@lem4481938 A K x k t i x' _51819 _51820) (@lem4481943 A K x k t i x' _51819 _51820)). Qed.
Lemma lem4481945 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : (term682 A K k t x _51819 _51820) = (term699 A K k t i x' _51819 _51820).
Proof. exact (EQ_MP (@lem4481944 A K x k t i x' _51819 _51820) (@lem4481935 A K _51819 _51820 k s t x i x' h1)). Qed.
Lemma lem4481946 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : term699 A K k t i x' _51819 _51820.
Proof. exact (EQ_MP (@lem4481945 A K _51819 _51820 k s t x i x' h2) (@lem4481382 A K _51819 _51820 k t x h1)). Qed.
Lemma lem4482050 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4482051 {A : Type'} (_51913 : A) (_51915 : A) (h1 : _51913 = _51915) : _51913 = _51915.
Proof. exact (h1). Qed.
Lemma lem4482052 {A : Type'} (_51914 : A -> Prop) (_51916 : A -> Prop) (h1 : _51914 = _51916) : _51914 = _51916.
Proof. exact (h1). Qed.
Lemma lem4482053 {A : Type'} (_51913 : A) (_51915 : A) (h1 : _51913 = _51915) : (@IN A _51913) = (@IN A _51915).
Proof. exact (MK_COMB (@lem4482050 A) (@lem4482051 A _51913 _51915 h1)). Qed.
Lemma lem4482054 {A : Type'} (_51913 : A) (_51915 : A) (_51914 : A -> Prop) (_51916 : A -> Prop) (h1 : _51913 = _51915) (h2 : _51914 = _51916) : (@IN A _51913 _51914) = (@IN A _51915 _51916).
Proof. exact (MK_COMB (@lem4482053 A _51913 _51915 h1) (@lem4482052 A _51914 _51916 h2)). Qed.
Lemma lem4482056 (b : Prop) (a : Prop) : term702 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4482057 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : term703 A _51915 _51916 _51913 _51914.
Proof. exact (@lem4482056 (@IN A _51915 _51916) (@IN A _51913 _51914)). Qed.
Lemma lem4482058 {A : Type'} (_51913 : A) (_51915 : A) (_51914 : A -> Prop) (_51916 : A -> Prop) (h1 : _51913 = _51915) (h2 : _51914 = _51916) : term704 A _51915 _51916 _51913 _51914.
Proof. exact (@lem4482057 A _51915 _51916 _51913 _51914 (@lem4482054 A _51913 _51915 _51914 _51916 h1 h2)). Qed.
Lemma lem4482059 {A : Type'} (_51916 : A -> Prop) (_51914 : A -> Prop) (_51913 : A) (_51915 : A) (h1 : _51913 = _51915) : term705 A _51915 _51916 _51913 _51914.
Proof. exact (fun h0 : _51914 = _51916 => @lem4482058 A _51913 _51915 _51914 _51916 h1 h0). Qed.
Lemma lem4482061 (a : Prop) (b : Prop) : (a -> b) = (term706 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4482062 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term705 A _51915 _51916 _51913 _51914) = (term707 A _51915 _51916 _51913 _51914).
Proof. exact (@lem4482061 (_51914 = _51916) (term704 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482063 {A : Type'} (_51916 : A -> Prop) (_51914 : A -> Prop) (_51913 : A) (_51915 : A) (h1 : _51913 = _51915) : term707 A _51915 _51916 _51913 _51914.
Proof. exact (EQ_MP (@lem4482062 A _51915 _51916 _51913 _51914) (@lem4482059 A _51916 _51914 _51913 _51915 h1)). Qed.
Lemma lem4482064 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : term708 A _51915 _51916 _51913 _51914.
Proof. exact (fun h0 : _51913 = _51915 => @lem4482063 A _51916 _51914 _51913 _51915 h0). Qed.
Lemma lem4482066 (a : Prop) (b : Prop) : (a -> b) = (term706 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4482067 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term708 A _51915 _51916 _51913 _51914) = (term709 A _51915 _51916 _51913 _51914).
Proof. exact (@lem4482066 (_51913 = _51915) (term707 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482068 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : term709 A _51915 _51916 _51913 _51914.
Proof. exact (EQ_MP (@lem4482067 A _51915 _51916 _51913 _51914) (@lem4482064 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482069 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4482070 {K : Type'} (_51917 : K) (_51918 : K) (h1 : _51917 = _51918) : _51917 = _51918.
Proof. exact (h1). Qed.
Lemma lem4482071 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) (h1 : _51917 = _51918) : (s _51917) = (s _51918).
Proof. exact (MK_COMB (@lem4482069 A K s) (@lem4482070 K _51917 _51918 h1)). Qed.
Lemma lem4482072 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : term710 A K _51917 s _51918.
Proof. exact (fun h0 : _51917 = _51918 => @lem4482071 A K s _51917 _51918 h0). Qed.
Lemma lem4482074 (a : Prop) (b : Prop) : (a -> b) = (term706 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4482075 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : (term710 A K _51917 s _51918) = (term711 A K _51917 s _51918).
Proof. exact (@lem4482074 (_51917 = _51918) ((s _51917) = (s _51918))). Qed.
Lemma lem4482076 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : term711 A K _51917 s _51918.
Proof. exact (EQ_MP (@lem4482075 A K _51917 s _51918) (@lem4482072 A K _51917 s _51918)). Qed.
Lemma lem4482147 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : @IN K i' k.
Proof. exact (proj1 (@lem4480214 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482148 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term712 K i' k.
Proof. exact (fun h0 : term677 K i' k => @lem4482147 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482150 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482151 {K : Type'} (i' : K) (k : K -> Prop) : (term712 K i' k) = (@IN K i' k).
Proof. exact (@lem4482150 (@IN K i' k)). Qed.
Lemma lem4482152 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : @IN K i' k.
Proof. exact (EQ_MP (@lem4482151 K i' k) (@lem4482148 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482154 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4481499 A K i x' i' x'' k s t x h1) (@lem4481200 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482155 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term714 A K i x' i' x''.
Proof. exact (fun h0 : term659 A K i x' i' x'' => @lem4482154 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482157 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482158 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) : (term714 A K i x' i' x'') = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (@lem4482157 ((@pair K A i x') = (@pair K A i' x''))). Qed.
Lemma lem4482159 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4482158 A K i x' i' x'') (@lem4482155 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482165 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4482166 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term695 A K _51755 _51757 _51756 _51758) = (term715 A K _51755 _51756 _51757 _51758).
Proof. exact (@lem4482165 (_51756 = _51758) (term659 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4482177 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term716 A K _51755 _51757 _51756 _51758) = (term717 A K _51755 _51756 _51757 _51758).
Proof. exact (MK_COMB (@lem4482176) (@lem4482166 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482187 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term715 A K _51755 _51756 _51757 _51758) = (term715 A K _51755 _51756 _51757 _51758).
Proof. exact (eq_refl (term715 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482188 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term695 A K _51755 _51757 _51756 _51758) = (term715 A K _51755 _51756 _51757 _51758)) = ((term715 A K _51755 _51756 _51757 _51758) = (term715 A K _51755 _51756 _51757 _51758)).
Proof. exact (MK_COMB (@lem4482177 A K _51755 _51756 _51757 _51758) (@lem4482187 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4482191 (x : Prop) : (x = x) = True.
Proof. exact (@lem4482190 Prop x). Qed.
Lemma lem4482192 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term715 A K _51755 _51756 _51757 _51758) = (term715 A K _51755 _51756 _51757 _51758)) = True.
Proof. exact (@lem4482191 (term715 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482193 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term695 A K _51755 _51757 _51756 _51758) = (term715 A K _51755 _51756 _51757 _51758)) = True.
Proof. exact (TRANS (@lem4482188 A K _51755 _51756 _51757 _51758) (@lem4482192 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482194 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : True = ((term695 A K _51755 _51757 _51756 _51758) = (term715 A K _51755 _51756 _51757 _51758)).
Proof. exact (SYM (@lem4482193 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482195 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term695 A K _51755 _51757 _51756 _51758) = (term715 A K _51755 _51756 _51757 _51758).
Proof. exact (EQ_MP (@lem4482194 A K _51755 _51756 _51757 _51758) (@lem0)). Qed.
Lemma lem4482196 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) (h1 : term153 A K) : term715 A K _51755 _51756 _51757 _51758.
Proof. exact (EQ_MP (@lem4482195 A K _51755 _51756 _51757 _51758) (@lem4481612 A K _51755 _51757 _51756 _51758 h1)). Qed.
Lemma lem4482198 (b : Prop) (a : Prop) : (a \/ b) = (term718 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4482199 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) : (term715 A K _51755 _51756 _51757 _51758) = (term719 A K _51755 _51757 _51756 _51758).
Proof. exact (@lem4482198 (term659 A K _51755 _51756 _51757 _51758) (_51756 = _51758)). Qed.
Lemma lem4482201 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482202 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term721 A K _51755 _51756 _51757 _51758) = ((@pair K A _51755 _51756) = (@pair K A _51757 _51758)).
Proof. exact (@lem4482201 ((@pair K A _51755 _51756) = (@pair K A _51757 _51758))). Qed.
Lemma lem4482203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4482204 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term722 A K _51755 _51756 _51757 _51758) = (term723 A K _51755 _51756 _51757 _51758).
Proof. exact (MK_COMB (@lem4482203) (@lem4482202 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482205 {A : Type'} (_51756 : A) (_51758 : A) : (_51756 = _51758) = (_51756 = _51758).
Proof. exact (eq_refl (_51756 = _51758)). Qed.
Lemma lem4482206 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) : (term719 A K _51755 _51757 _51756 _51758) = (term724 A K _51755 _51757 _51756 _51758).
Proof. exact (MK_COMB (@lem4482204 A K _51755 _51756 _51757 _51758) (@lem4482205 A _51756 _51758)). Qed.
Lemma lem4482207 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) : (term715 A K _51755 _51756 _51757 _51758) = (term724 A K _51755 _51757 _51756 _51758).
Proof. exact (TRANS (@lem4482199 A K _51755 _51757 _51756 _51758) (@lem4482206 A K _51755 _51757 _51756 _51758)). Qed.
Lemma lem4482210 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) (h1 : term153 A K) : term724 A K _51755 _51757 _51756 _51758.
Proof. exact (EQ_MP (@lem4482207 A K _51755 _51757 _51756 _51758) (@lem4482196 A K _51755 _51756 _51757 _51758 h1)). Qed.
Lemma lem4482211 {A K : Type'} (_51755 : K) (_51757 : K) (_51756 : A) (_51758 : A) (h1 : term153 A K) : term724 A K _51755 _51757 _51756 _51758.
Proof. exact (@lem4482210 A K _51755 _51757 _51756 _51758 h1). Qed.
Lemma lem4482212 {A K : Type'} (i : K) (i' : K) (x' : A) (x'' : A) (h1 : term153 A K) : term724 A K i i' x' x''.
Proof. exact (@lem4482211 A K i i' x' x'' h1). Qed.
Lemma lem4482215 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : x' = x''.
Proof. exact (@lem4482212 A K i i' x' x'' h1 (@lem4482159 A K i x' i' x'' k s t x h2)). Qed.
Lemma lem4482216 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term725 A x' x''.
Proof. exact (fun h0 : term726 A x' x'' => @lem4482215 A K i x' i' x'' k s t x h1 h2). Qed.
Lemma lem4482218 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482219 {A : Type'} (x' : A) (x'' : A) : (term725 A x' x'') = (x' = x'').
Proof. exact (@lem4482218 (x' = x'')). Qed.
Lemma lem4482220 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : x' = x''.
Proof. exact (EQ_MP (@lem4482219 A x' x'') (@lem4482216 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482222 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4481499 A K i x' i' x'' k s t x h1) (@lem4481200 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482223 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term714 A K i x' i' x''.
Proof. exact (fun h0 : term659 A K i x' i' x'' => @lem4482222 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482225 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482226 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) : (term714 A K i x' i' x'') = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (@lem4482225 ((@pair K A i x') = (@pair K A i' x''))). Qed.
Lemma lem4482227 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4482226 A K i x' i' x'') (@lem4482223 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482233 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4482234 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term694 A K _51756 _51758 _51755 _51757) = (term727 A K _51755 _51756 _51757 _51758).
Proof. exact (@lem4482233 (_51755 = _51757) (term659 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4482245 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term728 A K _51756 _51758 _51755 _51757) = (term729 A K _51755 _51756 _51757 _51758).
Proof. exact (MK_COMB (@lem4482244) (@lem4482234 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482255 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term727 A K _51755 _51756 _51757 _51758) = (term727 A K _51755 _51756 _51757 _51758).
Proof. exact (eq_refl (term727 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482256 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term694 A K _51756 _51758 _51755 _51757) = (term727 A K _51755 _51756 _51757 _51758)) = ((term727 A K _51755 _51756 _51757 _51758) = (term727 A K _51755 _51756 _51757 _51758)).
Proof. exact (MK_COMB (@lem4482245 A K _51755 _51756 _51757 _51758) (@lem4482255 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4482259 (x : Prop) : (x = x) = True.
Proof. exact (@lem4482258 Prop x). Qed.
Lemma lem4482260 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term727 A K _51755 _51756 _51757 _51758) = (term727 A K _51755 _51756 _51757 _51758)) = True.
Proof. exact (@lem4482259 (term727 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482261 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : ((term694 A K _51756 _51758 _51755 _51757) = (term727 A K _51755 _51756 _51757 _51758)) = True.
Proof. exact (TRANS (@lem4482256 A K _51755 _51756 _51757 _51758) (@lem4482260 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482262 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : True = ((term694 A K _51756 _51758 _51755 _51757) = (term727 A K _51755 _51756 _51757 _51758)).
Proof. exact (SYM (@lem4482261 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482263 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term694 A K _51756 _51758 _51755 _51757) = (term727 A K _51755 _51756 _51757 _51758).
Proof. exact (EQ_MP (@lem4482262 A K _51755 _51756 _51757 _51758) (@lem0)). Qed.
Lemma lem4482264 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) (h1 : term153 A K) : term727 A K _51755 _51756 _51757 _51758.
Proof. exact (EQ_MP (@lem4482263 A K _51755 _51756 _51757 _51758) (@lem4481598 A K _51756 _51758 _51755 _51757 h1)). Qed.
Lemma lem4482266 (b : Prop) (a : Prop) : (a \/ b) = (term718 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4482267 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) : (term727 A K _51755 _51756 _51757 _51758) = (term730 A K _51756 _51758 _51755 _51757).
Proof. exact (@lem4482266 (term659 A K _51755 _51756 _51757 _51758) (_51755 = _51757)). Qed.
Lemma lem4482269 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482270 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term721 A K _51755 _51756 _51757 _51758) = ((@pair K A _51755 _51756) = (@pair K A _51757 _51758)).
Proof. exact (@lem4482269 ((@pair K A _51755 _51756) = (@pair K A _51757 _51758))). Qed.
Lemma lem4482271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4482272 {A K : Type'} (_51755 : K) (_51756 : A) (_51757 : K) (_51758 : A) : (term722 A K _51755 _51756 _51757 _51758) = (term723 A K _51755 _51756 _51757 _51758).
Proof. exact (MK_COMB (@lem4482271) (@lem4482270 A K _51755 _51756 _51757 _51758)). Qed.
Lemma lem4482273 {K : Type'} (_51755 : K) (_51757 : K) : (_51755 = _51757) = (_51755 = _51757).
Proof. exact (eq_refl (_51755 = _51757)). Qed.
Lemma lem4482274 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) : (term730 A K _51756 _51758 _51755 _51757) = (term731 A K _51756 _51758 _51755 _51757).
Proof. exact (MK_COMB (@lem4482272 A K _51755 _51756 _51757 _51758) (@lem4482273 K _51755 _51757)). Qed.
Lemma lem4482275 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) : (term727 A K _51755 _51756 _51757 _51758) = (term731 A K _51756 _51758 _51755 _51757).
Proof. exact (TRANS (@lem4482267 A K _51756 _51758 _51755 _51757) (@lem4482274 A K _51756 _51758 _51755 _51757)). Qed.
Lemma lem4482278 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) (h1 : term153 A K) : term731 A K _51756 _51758 _51755 _51757.
Proof. exact (EQ_MP (@lem4482275 A K _51756 _51758 _51755 _51757) (@lem4482264 A K _51755 _51756 _51757 _51758 h1)). Qed.
Lemma lem4482279 {A K : Type'} (_51756 : A) (_51758 : A) (_51755 : K) (_51757 : K) (h1 : term153 A K) : term731 A K _51756 _51758 _51755 _51757.
Proof. exact (@lem4482278 A K _51756 _51758 _51755 _51757 h1). Qed.
Lemma lem4482280 {A K : Type'} (x' : A) (x'' : A) (i : K) (i' : K) (h1 : term153 A K) : term731 A K x' x'' i i'.
Proof. exact (@lem4482279 A K x' x'' i i' h1). Qed.
Lemma lem4482283 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : i = i'.
Proof. exact (@lem4482280 A K x' x'' i i' h1 (@lem4482227 A K i x' i' x'' k s t x h2)). Qed.
Lemma lem4482284 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term725 K i i'.
Proof. exact (fun h0 : term726 K i i' => @lem4482283 A K i x' i' x'' k s t x h1 h2). Qed.
Lemma lem4482286 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482287 {K : Type'} (i : K) (i' : K) : (term725 K i i') = (i = i').
Proof. exact (@lem4482286 (i = i')). Qed.
Lemma lem4482288 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : i = i'.
Proof. exact (EQ_MP (@lem4482287 K i i') (@lem4482284 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482294 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4482295 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : (term711 A K _51917 s _51918) = (term732 A K s _51917 _51918).
Proof. exact (@lem4482294 ((s _51917) = (s _51918)) (term726 K _51917 _51918)). Qed.
Lemma lem4482305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4482306 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : (term733 A K _51917 s _51918) = (term734 A K s _51917 _51918).
Proof. exact (MK_COMB (@lem4482305) (@lem4482295 A K s _51917 _51918)). Qed.
Lemma lem4482316 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : (term732 A K s _51917 _51918) = (term732 A K s _51917 _51918).
Proof. exact (eq_refl (term732 A K s _51917 _51918)). Qed.
Lemma lem4482317 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : ((term711 A K _51917 s _51918) = (term732 A K s _51917 _51918)) = ((term732 A K s _51917 _51918) = (term732 A K s _51917 _51918)).
Proof. exact (MK_COMB (@lem4482306 A K s _51917 _51918) (@lem4482316 A K s _51917 _51918)). Qed.
Lemma lem4482319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4482320 (x : Prop) : (x = x) = True.
Proof. exact (@lem4482319 Prop x). Qed.
Lemma lem4482321 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : ((term732 A K s _51917 _51918) = (term732 A K s _51917 _51918)) = True.
Proof. exact (@lem4482320 (term732 A K s _51917 _51918)). Qed.
Lemma lem4482322 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : ((term711 A K _51917 s _51918) = (term732 A K s _51917 _51918)) = True.
Proof. exact (TRANS (@lem4482317 A K s _51917 _51918) (@lem4482321 A K s _51917 _51918)). Qed.
Lemma lem4482323 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : True = ((term711 A K _51917 s _51918) = (term732 A K s _51917 _51918)).
Proof. exact (SYM (@lem4482322 A K s _51917 _51918)). Qed.
Lemma lem4482324 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : (term711 A K _51917 s _51918) = (term732 A K s _51917 _51918).
Proof. exact (EQ_MP (@lem4482323 A K s _51917 _51918) (@lem0)). Qed.
Lemma lem4482325 {A K : Type'} (s : type1470 A K) (_51917 : K) (_51918 : K) : term732 A K s _51917 _51918.
Proof. exact (EQ_MP (@lem4482324 A K s _51917 _51918) (@lem4482076 A K _51917 s _51918)). Qed.
Lemma lem4482327 (b : Prop) (a : Prop) : (a \/ b) = (term718 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4482328 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : (term732 A K s _51917 _51918) = (term735 A K _51917 s _51918).
Proof. exact (@lem4482327 (term726 K _51917 _51918) ((s _51917) = (s _51918))). Qed.
Lemma lem4482330 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482331 {K : Type'} (_51917 : K) (_51918 : K) : (term736 K _51917 _51918) = (_51917 = _51918).
Proof. exact (@lem4482330 (_51917 = _51918)). Qed.
Lemma lem4482332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4482333 {K : Type'} (_51917 : K) (_51918 : K) : (term737 K _51917 _51918) = (term738 K _51917 _51918).
Proof. exact (MK_COMB (@lem4482332) (@lem4482331 K _51917 _51918)). Qed.
Lemma lem4482334 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : ((s _51917) = (s _51918)) = ((s _51917) = (s _51918)).
Proof. exact (eq_refl ((s _51917) = (s _51918))). Qed.
Lemma lem4482335 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : (term735 A K _51917 s _51918) = (term710 A K _51917 s _51918).
Proof. exact (MK_COMB (@lem4482333 K _51917 _51918) (@lem4482334 A K _51917 s _51918)). Qed.
Lemma lem4482336 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : (term732 A K s _51917 _51918) = (term710 A K _51917 s _51918).
Proof. exact (TRANS (@lem4482328 A K _51917 s _51918) (@lem4482335 A K _51917 s _51918)). Qed.
Lemma lem4482339 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : term710 A K _51917 s _51918.
Proof. exact (EQ_MP (@lem4482336 A K _51917 s _51918) (@lem4482325 A K s _51917 _51918)). Qed.
Lemma lem4482340 {A K : Type'} (_51917 : K) (s : type1470 A K) (_51918 : K) : term710 A K _51917 s _51918.
Proof. exact (@lem4482339 A K _51917 s _51918). Qed.
Lemma lem4482341 {A K : Type'} (i : K) (s : type1470 A K) (i' : K) : term710 A K i s i'.
Proof. exact (@lem4482340 A K i s i'). Qed.
Lemma lem4482344 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : (s i) = (s i').
Proof. exact (@lem4482341 A K i s i' (@lem4482288 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482345 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term739 A K i s i'.
Proof. exact (fun h0 : term740 A K i s i' => @lem4482344 A K i x' i' x'' k s t x h1 h2). Qed.
Lemma lem4482347 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482348 {A K : Type'} (i : K) (s : type1470 A K) (i' : K) : (term739 A K i s i') = ((s i) = (s i')).
Proof. exact (@lem4482347 ((s i) = (s i'))). Qed.
Lemma lem4482349 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : (s i) = (s i').
Proof. exact (EQ_MP (@lem4482348 A K i s i') (@lem4482345 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482351 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term208 A K x' s i.
Proof. exact (proj2 (@lem4480218 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482352 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term741 A K x' s i.
Proof. exact (fun h0 : term680 A K x' s i => @lem4482351 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482354 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482355 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) : (term741 A K x' s i) = (term208 A K x' s i).
Proof. exact (@lem4482354 (term208 A K x' s i)). Qed.
Lemma lem4482356 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term208 A K x' s i.
Proof. exact (EQ_MP (@lem4482355 A K x' s i) (@lem4482352 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482374 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4482375 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term707 A _51915 _51916 _51913 _51914) = (term742 A _51915 _51916 _51913 _51914).
Proof. exact (@lem4482374 (@IN A _51915 _51916) (term743 A _51914 _51916) (term677 A _51913 _51914)). Qed.
Lemma lem4482393 {A : Type'} (_51913 : A) (_51915 : A) : (term744 A _51913 _51915) = (term744 A _51913 _51915).
Proof. exact (eq_refl (term744 A _51913 _51915)). Qed.
Lemma lem4482394 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term709 A _51915 _51916 _51913 _51914) = (term745 A _51915 _51916 _51913 _51914).
Proof. exact (MK_COMB (@lem4482393 A _51913 _51915) (@lem4482375 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482398 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4482399 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term745 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914).
Proof. exact (@lem4482398 (@IN A _51915 _51916) (term726 A _51913 _51915) (term747 A _51916 _51913 _51914)). Qed.
Lemma lem4482429 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term709 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914).
Proof. exact (TRANS (@lem4482394 A _51915 _51916 _51913 _51914) (@lem4482399 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4482431 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term748 A _51915 _51916 _51913 _51914) = (term749 A _51915 _51916 _51913 _51914).
Proof. exact (MK_COMB (@lem4482430) (@lem4482429 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482461 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term746 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914).
Proof. exact (eq_refl (term746 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482462 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : ((term709 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914)) = ((term746 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914)).
Proof. exact (MK_COMB (@lem4482431 A _51915 _51916 _51913 _51914) (@lem4482461 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482464 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4482465 (x : Prop) : (x = x) = True.
Proof. exact (@lem4482464 Prop x). Qed.
Lemma lem4482466 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : ((term746 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914)) = True.
Proof. exact (@lem4482465 (term746 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482467 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : ((term709 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914)) = True.
Proof. exact (TRANS (@lem4482462 A _51915 _51916 _51913 _51914) (@lem4482466 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482468 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : True = ((term709 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914)).
Proof. exact (SYM (@lem4482467 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482469 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term709 A _51915 _51916 _51913 _51914) = (term746 A _51915 _51916 _51913 _51914).
Proof. exact (EQ_MP (@lem4482468 A _51915 _51916 _51913 _51914) (@lem0)). Qed.
Lemma lem4482470 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : term746 A _51915 _51916 _51913 _51914.
Proof. exact (EQ_MP (@lem4482469 A _51915 _51916 _51913 _51914) (@lem4482068 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482472 (b : Prop) (a : Prop) : (a \/ b) = (term718 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4482473 {A : Type'} (_51913 : A) (_51914 : A -> Prop) (_51915 : A) (_51916 : A -> Prop) : (term746 A _51915 _51916 _51913 _51914) = (term750 A _51913 _51914 _51915 _51916).
Proof. exact (@lem4482472 (term751 A _51915 _51916 _51913 _51914) (@IN A _51915 _51916)). Qed.
Lemma lem4482475 (a : Prop) (b : Prop) : (term752 a b) = (term753 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4482476 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term754 A _51915 _51916 _51913 _51914) = (term755 A _51915 _51916 _51913 _51914).
Proof. exact (@lem4482475 (term726 A _51913 _51915) (term747 A _51916 _51913 _51914)). Qed.
Lemma lem4482478 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482479 {A : Type'} (_51913 : A) (_51915 : A) : (term736 A _51913 _51915) = (_51913 = _51915).
Proof. exact (@lem4482478 (_51913 = _51915)). Qed.
Lemma lem4482480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4482481 {A : Type'} (_51913 : A) (_51915 : A) : (term756 A _51913 _51915) = (term757 A _51913 _51915).
Proof. exact (MK_COMB (@lem4482480) (@lem4482479 A _51913 _51915)). Qed.
Lemma lem4482483 (a : Prop) (b : Prop) : (term752 a b) = (term753 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4482484 {A : Type'} (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term758 A _51916 _51913 _51914) = (term759 A _51916 _51913 _51914).
Proof. exact (@lem4482483 (term743 A _51914 _51916) (term677 A _51913 _51914)). Qed.
Lemma lem4482486 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482487 {A : Type'} (_51914 : A -> Prop) (_51916 : A -> Prop) : (term760 A _51914 _51916) = (_51914 = _51916).
Proof. exact (@lem4482486 (_51914 = _51916)). Qed.
Lemma lem4482488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4482489 {A : Type'} (_51914 : A -> Prop) (_51916 : A -> Prop) : (term761 A _51914 _51916) = (term762 A _51914 _51916).
Proof. exact (MK_COMB (@lem4482488) (@lem4482487 A _51914 _51916)). Qed.
Lemma lem4482491 (a : Prop) : (term720 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4482492 {A : Type'} (_51913 : A) (_51914 : A -> Prop) : (term763 A _51913 _51914) = (@IN A _51913 _51914).
Proof. exact (@lem4482491 (@IN A _51913 _51914)). Qed.
Lemma lem4482493 {A : Type'} (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term759 A _51916 _51913 _51914) = (term764 A _51916 _51913 _51914).
Proof. exact (MK_COMB (@lem4482489 A _51914 _51916) (@lem4482492 A _51913 _51914)). Qed.
Lemma lem4482494 {A : Type'} (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term758 A _51916 _51913 _51914) = (term764 A _51916 _51913 _51914).
Proof. exact (TRANS (@lem4482484 A _51916 _51913 _51914) (@lem4482493 A _51916 _51913 _51914)). Qed.
Lemma lem4482495 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term755 A _51915 _51916 _51913 _51914) = (term765 A _51915 _51916 _51913 _51914).
Proof. exact (MK_COMB (@lem4482481 A _51913 _51915) (@lem4482494 A _51916 _51913 _51914)). Qed.
Lemma lem4482496 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term754 A _51915 _51916 _51913 _51914) = (term765 A _51915 _51916 _51913 _51914).
Proof. exact (TRANS (@lem4482476 A _51915 _51916 _51913 _51914) (@lem4482495 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4482498 {A : Type'} (_51915 : A) (_51916 : A -> Prop) (_51913 : A) (_51914 : A -> Prop) : (term766 A _51915 _51916 _51913 _51914) = (term767 A _51915 _51916 _51913 _51914).
Proof. exact (MK_COMB (@lem4482497) (@lem4482496 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482499 {A : Type'} (_51915 : A) (_51916 : A -> Prop) : (@IN A _51915 _51916) = (@IN A _51915 _51916).
Proof. exact (eq_refl (@IN A _51915 _51916)). Qed.
Lemma lem4482500 {A : Type'} (_51913 : A) (_51914 : A -> Prop) (_51915 : A) (_51916 : A -> Prop) : (term750 A _51913 _51914 _51915 _51916) = (term768 A _51913 _51914 _51915 _51916).
Proof. exact (MK_COMB (@lem4482498 A _51915 _51916 _51913 _51914) (@lem4482499 A _51915 _51916)). Qed.
Lemma lem4482501 {A : Type'} (_51913 : A) (_51914 : A -> Prop) (_51915 : A) (_51916 : A -> Prop) : (term746 A _51915 _51916 _51913 _51914) = (term768 A _51913 _51914 _51915 _51916).
Proof. exact (TRANS (@lem4482473 A _51913 _51914 _51915 _51916) (@lem4482500 A _51913 _51914 _51915 _51916)). Qed.
Lemma lem4482503 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term769 A K i' x' s i.
Proof. exact (conj (@lem4482349 A K i x' i' x'' k s t x h1 h2) (@lem4482356 A K i x' i' x'' k s t x h2)). Qed.
Lemma lem4482504 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term770 A K x'' i' x' s i.
Proof. exact (conj (@lem4482220 A K i x' i' x'' k s t x h1 h2) (@lem4482503 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482506 {A : Type'} (_51913 : A) (_51914 : A -> Prop) (_51915 : A) (_51916 : A -> Prop) : term768 A _51913 _51914 _51915 _51916.
Proof. exact (EQ_MP (@lem4482501 A _51913 _51914 _51915 _51916) (@lem4482470 A _51915 _51916 _51913 _51914)). Qed.
Lemma lem4482507 {A : Type'} (_51913 : A) (_51914 : A -> Prop) (_51915 : A) (_51916 : A -> Prop) : term768 A _51913 _51914 _51915 _51916.
Proof. exact (@lem4482506 A _51913 _51914 _51915 _51916). Qed.
Lemma lem4482508 {A K : Type'} (x' : A) (i : K) (x'' : A) (s : type1470 A K) (i' : K) : term771 A K x' i x'' s i'.
Proof. exact (@lem4482507 A x' (s i) x'' (s i')). Qed.
Lemma lem4482511 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term208 A K x'' s i'.
Proof. exact (@lem4482508 A K x' i x'' s i' (@lem4482504 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482512 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term741 A K x'' s i'.
Proof. exact (fun h0 : term680 A K x'' s i' => @lem4482511 A K i x' i' x'' k s t x h1 h2). Qed.
Lemma lem4482514 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482515 {A K : Type'} (x'' : A) (s : type1470 A K) (i' : K) : (term741 A K x'' s i') = (term208 A K x'' s i').
Proof. exact (@lem4482514 (term208 A K x'' s i')). Qed.
Lemma lem4482516 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term208 A K x'' s i'.
Proof. exact (EQ_MP (@lem4482515 A K x'' s i') (@lem4482512 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482518 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term208 A K x'' t i'.
Proof. exact (proj2 (@lem4480214 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482519 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term741 A K x'' t i'.
Proof. exact (fun h0 : term680 A K x'' t i' => @lem4482518 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482521 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482522 {A K : Type'} (x'' : A) (t : type1470 A K) (i' : K) : (term741 A K x'' t i') = (term208 A K x'' t i').
Proof. exact (@lem4482521 (term208 A K x'' t i')). Qed.
Lemma lem4482523 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term208 A K x'' t i'.
Proof. exact (EQ_MP (@lem4482522 A K x'' t i') (@lem4482519 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482525 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4481499 A K i x' i' x'' k s t x h1) (@lem4481200 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482526 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term714 A K i x' i' x''.
Proof. exact (fun h0 : term659 A K i x' i' x'' => @lem4482525 A K i x' i' x'' k s t x h1). Qed.
Lemma lem4482528 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482529 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) : (term714 A K i x' i' x'') = ((@pair K A i x') = (@pair K A i' x'')).
Proof. exact (@lem4482528 ((@pair K A i x') = (@pair K A i' x''))). Qed.
Lemma lem4482530 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : (@pair K A i x') = (@pair K A i' x'').
Proof. exact (EQ_MP (@lem4482529 A K i x' i' x'') (@lem4482526 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482532 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482533 {A K : Type'} (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term774 A K t i x' _51767 _51768) = (term775 A K t i x' _51767 _51768).
Proof. exact (@lem4482532 (term208 A K _51768 t _51767) ((@pair K A i x') = (@pair K A _51767 _51768))). Qed.
Lemma lem4482534 {A K : Type'} (_51768 : A) (s : type1470 A K) (_51767 : K) : (term776 A K _51768 s _51767) = (term776 A K _51768 s _51767).
Proof. exact (eq_refl (term776 A K _51768 s _51767)). Qed.
Lemma lem4482535 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term777 A K s t i x' _51767 _51768) = (term778 A K s t i x' _51767 _51768).
Proof. exact (MK_COMB (@lem4482534 A K _51768 s _51767) (@lem4482533 A K t i x' _51767 _51768)). Qed.
Lemma lem4482537 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482538 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term778 A K s t i x' _51767 _51768) = (term779 A K s t i x' _51767 _51768).
Proof. exact (@lem4482537 (term208 A K _51768 s _51767) (term780 A K t i x' _51767 _51768)). Qed.
Lemma lem4482539 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term777 A K s t i x' _51767 _51768) = (term779 A K s t i x' _51767 _51768).
Proof. exact (TRANS (@lem4482535 A K s t i x' _51767 _51768) (@lem4482538 A K s t i x' _51767 _51768)). Qed.
Lemma lem4482540 {K : Type'} (_51767 : K) (k : K -> Prop) : (term238 K _51767 k) = (term238 K _51767 k).
Proof. exact (eq_refl (term238 K _51767 k)). Qed.
Lemma lem4482541 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term686 A K k s t i x' _51767 _51768) = (term781 A K k s t i x' _51767 _51768).
Proof. exact (MK_COMB (@lem4482540 K _51767 k) (@lem4482539 A K s t i x' _51767 _51768)). Qed.
Lemma lem4482543 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482544 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term781 A K k s t i x' _51767 _51768) = (term782 A K k s t i x' _51767 _51768).
Proof. exact (@lem4482543 (@IN K _51767 k) (term783 A K s t i x' _51767 _51768)). Qed.
Lemma lem4482545 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term686 A K k s t i x' _51767 _51768) = (term782 A K k s t i x' _51767 _51768).
Proof. exact (TRANS (@lem4482541 A K k s t i x' _51767 _51768) (@lem4482544 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4482547 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4482548 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term782 A K k s t i x' _51767 _51768) = (term784 A K k s t i x' _51767 _51768).
Proof. exact (@lem4482547 (term785 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4482549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) (_51767 : K) (_51768 : A) : (term686 A K k s t i x' _51767 _51768) = (term784 A K k s t i x' _51767 _51768).
Proof. exact (TRANS (@lem4482545 A K k s t i x' _51767 _51768) (@lem4482548 A K k s t i x' _51767 _51768)). Qed.
Lemma lem4482551 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term780 A K t i x' i' x''.
Proof. exact (conj (@lem4482523 A K i x' i' x'' k s t x h1) (@lem4482530 A K i x' i' x'' k s t x h1)). Qed.
Lemma lem4482552 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term783 A K s t i x' i' x''.
Proof. exact (conj (@lem4482516 A K i x' i' x'' k s t x h1 h2) (@lem4482551 A K i x' i' x'' k s t x h2)). Qed.
Lemma lem4482553 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term785 A K k s t i x' i' x''.
Proof. exact (conj (@lem4482152 A K i x' i' x'' k s t x h2) (@lem4482552 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482555 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term784 A K k s t i x' _51767 _51768.
Proof. exact (EQ_MP (@lem4482549 A K k s t i x' _51767 _51768) (@lem4481487 A K _51767 _51768 i x' i' x'' k s t x h1)). Qed.
Lemma lem4482556 {A K : Type'} (_51767 : K) (_51768 : A) (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term784 A K k s t i x' _51767 _51768.
Proof. exact (@lem4482555 A K _51767 _51768 i x' i' x'' k s t x h1). Qed.
Lemma lem4482557 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term418 A K i x' i' x'' k s t x) : term784 A K k s t i x' i' x''.
Proof. exact (@lem4482556 A K i' x'' i x' i' x'' k s t x h1). Qed.
Lemma lem4482560 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : False.
Proof. exact (@lem4482557 A K i x' i' x'' k s t x h2 (@lem4482553 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482561 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : term786.
Proof. exact (fun h0 : ~ False => @lem4482560 A K i x' i' x'' k s t x h1 h2). Qed.
Lemma lem4482563 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482564 : term786 = False.
Proof. exact (@lem4482563 False). Qed.
Lemma lem4482682 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : @IN K i k.
Proof. exact (proj1 (@lem4480224 A K k s t x i x' h1)). Qed.
Lemma lem4482683 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term712 K i k.
Proof. exact (fun h0 : term677 K i k => @lem4482682 A K k s t x i x' h1). Qed.
Lemma lem4482685 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482686 {K : Type'} (i : K) (k : K -> Prop) : (term712 K i k) = (@IN K i k).
Proof. exact (@lem4482685 (@IN K i k)). Qed.
Lemma lem4482687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4482686 K i k) (@lem4482683 A K k s t x i x' h1)). Qed.
Lemma lem4482689 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term208 A K x' s i.
Proof. exact (proj1 (@lem4480225 A K k s t x i x' h1)). Qed.
Lemma lem4482690 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term741 A K x' s i.
Proof. exact (fun h0 : term680 A K x' s i => @lem4482689 A K k s t x i x' h1). Qed.
Lemma lem4482692 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482693 {A K : Type'} (x' : A) (s : type1470 A K) (i : K) : (term741 A K x' s i) = (term208 A K x' s i).
Proof. exact (@lem4482692 (term208 A K x' s i)). Qed.
Lemma lem4482694 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term208 A K x' s i.
Proof. exact (EQ_MP (@lem4482693 A K x' s i) (@lem4482690 A K k s t x i x' h1)). Qed.
Lemma lem4482696 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4482697 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4482696 A K x). Qed.
Lemma lem4482698 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4482697 A K (@pair K A i x')). Qed.
Lemma lem4482699 {A K : Type'} (i : K) (x' : A) : term787 A K i x'.
Proof. exact (fun h0 : term788 A K i x' => @lem4482698 A K i x'). Qed.
Lemma lem4482701 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482702 {A K : Type'} (i : K) (x' : A) : (term787 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4482701 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4482703 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4482702 A K i x') (@lem4482699 A K i x')). Qed.
Lemma lem4482705 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482706 {A K : Type'} (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term774 A K s i x' _51793 _51794) = (term775 A K s i x' _51793 _51794).
Proof. exact (@lem4482705 (term208 A K _51794 s _51793) ((@pair K A i x') = (@pair K A _51793 _51794))). Qed.
Lemma lem4482707 {K : Type'} (_51793 : K) (k : K -> Prop) : (term238 K _51793 k) = (term238 K _51793 k).
Proof. exact (eq_refl (term238 K _51793 k)). Qed.
Lemma lem4482708 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term699 A K k s i x' _51793 _51794) = (term789 A K k s i x' _51793 _51794).
Proof. exact (MK_COMB (@lem4482707 K _51793 k) (@lem4482706 A K s i x' _51793 _51794)). Qed.
Lemma lem4482710 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term789 A K k s i x' _51793 _51794) = (term790 A K k s i x' _51793 _51794).
Proof. exact (@lem4482710 (@IN K _51793 k) (term780 A K s i x' _51793 _51794)). Qed.
Lemma lem4482712 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term699 A K k s i x' _51793 _51794) = (term790 A K k s i x' _51793 _51794).
Proof. exact (TRANS (@lem4482708 A K k s i x' _51793 _51794) (@lem4482711 A K k s i x' _51793 _51794)). Qed.
Lemma lem4482714 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4482715 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term790 A K k s i x' _51793 _51794) = (term791 A K k s i x' _51793 _51794).
Proof. exact (@lem4482714 (term792 A K k s i x' _51793 _51794)). Qed.
Lemma lem4482716 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x' : A) (_51793 : K) (_51794 : A) : (term699 A K k s i x' _51793 _51794) = (term791 A K k s i x' _51793 _51794).
Proof. exact (TRANS (@lem4482712 A K k s i x' _51793 _51794) (@lem4482715 A K k s i x' _51793 _51794)). Qed.
Lemma lem4482718 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term793 A K s i x'.
Proof. exact (conj (@lem4482694 A K k s t x i x' h1) (@lem4482703 A K i x')). Qed.
Lemma lem4482719 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term794 A K k s i x'.
Proof. exact (conj (@lem4482687 A K k s t x i x' h1) (@lem4482718 A K k s t x i x' h1)). Qed.
Lemma lem4482721 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : term791 A K k s i x' _51793 _51794.
Proof. exact (EQ_MP (@lem4482716 A K k s i x' _51793 _51794) (@lem4481751 A K _51793 _51794 k s t x i x' h1 h2)). Qed.
Lemma lem4482722 {A K : Type'} (_51793 : K) (_51794 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : term791 A K k s i x' _51793 _51794.
Proof. exact (@lem4482721 A K _51793 _51794 k s t x i x' h1 h2). Qed.
Lemma lem4482723 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : term795 A K k s i x'.
Proof. exact (@lem4482722 A K i x' k s t x i x' h1 h2). Qed.
Lemma lem4482726 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (@lem4482723 A K k s t x i x' h1 h2 (@lem4482719 A K k s t x i x' h2)). Qed.
Lemma lem4482727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : term786.
Proof. exact (fun h0 : ~ False => @lem4482726 A K k s t x i x' h1 h2). Qed.
Lemma lem4482729 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482730 : term786 = False.
Proof. exact (@lem4482729 False). Qed.
Lemma lem4482848 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : @IN K i k.
Proof. exact (proj1 (@lem4480224 A K k s t x i x' h1)). Qed.
Lemma lem4482849 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term712 K i k.
Proof. exact (fun h0 : term677 K i k => @lem4482848 A K k s t x i x' h1). Qed.
Lemma lem4482851 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482852 {K : Type'} (i : K) (k : K -> Prop) : (term712 K i k) = (@IN K i k).
Proof. exact (@lem4482851 (@IN K i k)). Qed.
Lemma lem4482853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : @IN K i k.
Proof. exact (EQ_MP (@lem4482852 K i k) (@lem4482849 A K k s t x i x' h1)). Qed.
Lemma lem4482855 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term208 A K x' t i.
Proof. exact (proj2 (@lem4480225 A K k s t x i x' h1)). Qed.
Lemma lem4482856 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term741 A K x' t i.
Proof. exact (fun h0 : term680 A K x' t i => @lem4482855 A K k s t x i x' h1). Qed.
Lemma lem4482858 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482859 {A K : Type'} (x' : A) (t : type1470 A K) (i : K) : (term741 A K x' t i) = (term208 A K x' t i).
Proof. exact (@lem4482858 (term208 A K x' t i)). Qed.
Lemma lem4482860 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term208 A K x' t i.
Proof. exact (EQ_MP (@lem4482859 A K x' t i) (@lem4482856 A K k s t x i x' h1)). Qed.
Lemma lem4482862 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem21386 (prod K A) x). Qed.
Lemma lem4482863 {A K : Type'} (x : prod K A) : x = x.
Proof. exact (@lem4482862 A K x). Qed.
Lemma lem4482864 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (@lem4482863 A K (@pair K A i x')). Qed.
Lemma lem4482865 {A K : Type'} (i : K) (x' : A) : term787 A K i x'.
Proof. exact (fun h0 : term788 A K i x' => @lem4482864 A K i x'). Qed.
Lemma lem4482867 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482868 {A K : Type'} (i : K) (x' : A) : (term787 A K i x') = ((@pair K A i x') = (@pair K A i x')).
Proof. exact (@lem4482867 ((@pair K A i x') = (@pair K A i x'))). Qed.
Lemma lem4482869 {A K : Type'} (i : K) (x' : A) : (@pair K A i x') = (@pair K A i x').
Proof. exact (EQ_MP (@lem4482868 A K i x') (@lem4482865 A K i x')). Qed.
Lemma lem4482871 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482872 {A K : Type'} (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term774 A K t i x' _51819 _51820) = (term775 A K t i x' _51819 _51820).
Proof. exact (@lem4482871 (term208 A K _51820 t _51819) ((@pair K A i x') = (@pair K A _51819 _51820))). Qed.
Lemma lem4482873 {K : Type'} (_51819 : K) (k : K -> Prop) : (term238 K _51819 k) = (term238 K _51819 k).
Proof. exact (eq_refl (term238 K _51819 k)). Qed.
Lemma lem4482874 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term699 A K k t i x' _51819 _51820) = (term789 A K k t i x' _51819 _51820).
Proof. exact (MK_COMB (@lem4482873 K _51819 k) (@lem4482872 A K t i x' _51819 _51820)). Qed.
Lemma lem4482876 (a : Prop) (b : Prop) : (term772 a b) = (term773 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4482877 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term789 A K k t i x' _51819 _51820) = (term790 A K k t i x' _51819 _51820).
Proof. exact (@lem4482876 (@IN K _51819 k) (term780 A K t i x' _51819 _51820)). Qed.
Lemma lem4482878 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term699 A K k t i x' _51819 _51820) = (term790 A K k t i x' _51819 _51820).
Proof. exact (TRANS (@lem4482874 A K k t i x' _51819 _51820) (@lem4482877 A K k t i x' _51819 _51820)). Qed.
Lemma lem4482880 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4482881 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term790 A K k t i x' _51819 _51820) = (term791 A K k t i x' _51819 _51820).
Proof. exact (@lem4482880 (term792 A K k t i x' _51819 _51820)). Qed.
Lemma lem4482882 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (i : K) (x' : A) (_51819 : K) (_51820 : A) : (term699 A K k t i x' _51819 _51820) = (term791 A K k t i x' _51819 _51820).
Proof. exact (TRANS (@lem4482878 A K k t i x' _51819 _51820) (@lem4482881 A K k t i x' _51819 _51820)). Qed.
Lemma lem4482884 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term793 A K t i x'.
Proof. exact (conj (@lem4482860 A K k s t x i x' h1) (@lem4482869 A K i x')). Qed.
Lemma lem4482885 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : term794 A K k t i x'.
Proof. exact (conj (@lem4482853 A K k s t x i x' h1) (@lem4482884 A K k s t x i x' h1)). Qed.
Lemma lem4482887 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : term791 A K k t i x' _51819 _51820.
Proof. exact (EQ_MP (@lem4482882 A K k t i x' _51819 _51820) (@lem4481946 A K _51819 _51820 k s t x i x' h1 h2)). Qed.
Lemma lem4482888 {A K : Type'} (_51819 : K) (_51820 : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : term791 A K k t i x' _51819 _51820.
Proof. exact (@lem4482887 A K _51819 _51820 k s t x i x' h1 h2). Qed.
Lemma lem4482889 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : term795 A K k t i x'.
Proof. exact (@lem4482888 A K i x' k s t x i x' h1 h2). Qed.
Lemma lem4482892 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (@lem4482889 A K k s t x i x' h1 h2 (@lem4482885 A K k s t x i x' h2)). Qed.
Lemma lem4482893 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : term786.
Proof. exact (fun h0 : ~ False => @lem4482892 A K k s t x i x' h1 h2). Qed.
Lemma lem4482895 (p : Prop) : (term713 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4482896 : term786 = False.
Proof. exact (@lem4482895 False). Qed.
Lemma lem4482898 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (EQ_MP (@lem4482896) (@lem4482893 A K k s t x i x' h1 h2)). Qed.
Lemma lem4482899 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (EQ_MP (@lem4482730) (@lem4482727 A K k s t x i x' h1 h2)). Qed.
Lemma lem4482900 {A K : Type'} (i : K) (x' : A) (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term418 A K i x' i' x'' k s t x) : False.
Proof. exact (EQ_MP (@lem4482564) (@lem4482561 A K i x' i' x'' k s t x h1 h2)). Qed.
Lemma lem4482901 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : (term230 A K k t x) = False.
Proof. exact (prop_ext (fun h3 : term230 A K k t x => @lem4482898 A K k s t x i x' h1 h2) (fun h3 : False => @lem4480898 A K k t x h1)). Qed.
Lemma lem4482902 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k t x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (EQ_MP (@lem4482901 A K k s t x i x' h1 h2) (@lem4480898 A K k t x h1)). Qed.
Lemma lem4482903 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : (term230 A K k s x) = False.
Proof. exact (prop_ext (fun h3 : term230 A K k s x => @lem4482899 A K k s t x i x' h1 h2) (fun h3 : False => @lem4480680 A K k s x h1)). Qed.
Lemma lem4482904 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term230 A K k s x) (h2 : term449 A K k s t x i x') : False.
Proof. exact (EQ_MP (@lem4482903 A K k s t x i x' h1 h2) (@lem4480680 A K k s x h1)). Qed.
Lemma lem4482905 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term449 A K k s t x i x') : False.
Proof. exact (or_elim (@lem4480222 A K k s t x i x' h1) (fun h0 : term230 A K k s x => @lem4482904 A K k s t x i x' h0 h1) (fun h0 : term230 A K k t x => @lem4482902 A K k s t x i x' h0 h1)). Qed.
Lemma lem4482906 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term153 A K) (h2 : term540 A K i' x'' k s t x i x') : False.
Proof. exact (or_elim (@lem4480200 A K i' x'' k s t x i x' h2) (fun h0 : term418 A K i x' i' x'' k s t x => @lem4482900 A K i x' i' x'' k s t x h1 h0) (fun h0 : term449 A K k s t x i x' => @lem4482905 A K k s t x i x' h0)). Qed.
Lemma lem4482907 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term153 A K) (h2 : term540 A K i' x'' k s t x i x') : (term540 A K i' x'' k s t x i x') = False.
Proof. exact (prop_ext (fun h3 : term540 A K i' x'' k s t x i x' => @lem4482906 A K i' x'' k s t x i x' h1 h2) (fun h3 : False => @lem4480200 A K i' x'' k s t x i x' h2)). Qed.
Lemma lem4482908 {A K : Type'} (i' : K) (x'' : A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term153 A K) (h2 : term540 A K i' x'' k s t x i x') : False.
Proof. exact (EQ_MP (@lem4482907 A K i' x'' k s t x i x' h1 h2) (@lem4480200 A K i' x'' k s t x i x' h2)). Qed.
Lemma lem4482909 {A K : Type'} (i' : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term153 A K) (h2 : term543 A K i' k s t x i x') : False.
Proof. exact (ex_elim (@lem4479687 A K i' k s t x i x' h2) (fun x'' : A => fun h0 : term542 A K i' k s t x i x' x'' => @lem4482908 A K i' x'' k s t x i x' h1 h0)). Qed.
Lemma lem4482910 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (x' : A) (h1 : term153 A K) (h2 : term545 A K k s t x i x') : False.
Proof. exact (ex_elim (@lem4479686 A K k s t x i x' h2) (fun i' : K => fun h0 : term544 A K k s t x i x' i' => @lem4482909 A K i' k s t x i x' h1 h0)). Qed.
Lemma lem4482911 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (i : K) (h1 : term153 A K) (h2 : term547 A K k s t x i) : False.
Proof. exact (ex_elim (@lem4479685 A K k s t x i h2) (fun x' : A => fun h0 : term546 A K k s t x i x' => @lem4482910 A K k s t x i x' h1 h0)). Qed.
Lemma lem4482912 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : prod K A) (h1 : term153 A K) (h2 : term549 A K k s t x) : False.
Proof. exact (ex_elim (@lem4479684 A K k s t x h2) (fun i : K => fun h0 : term548 A K k s t x i => @lem4482911 A K k s t x i h1 h0)). Qed.
Lemma lem4482913 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term153 A K) (h2 : term152 A K k s t) : False.
Proof. exact (ex_elim (@lem4477868 A K k s t h2) (fun x : prod K A => fun h0 : term550 A K k s t x => @lem4482912 A K k s t x h1 h0)). Qed.
Lemma lem4482914 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term153 A K) (h2 : term152 A K k s t) : term160 A B K.
Proof. exact (fun h0 : term154 A B K => @lem4482913 A K k s t h1 h2). Qed.
Lemma lem4482915 {A B K : Type'} : (term160 A B K) = (term161 A B K).
Proof. exact (@lem69 (term154 A B K)). Qed.
Lemma lem4482916 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term153 A K) (h2 : term152 A K k s t) : term161 A B K.
Proof. exact (EQ_MP (@lem4482915 A B K) (@lem4482914 A B K k s t h1 h2)). Qed.
Lemma lem4482917 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term164 A B K.
Proof. exact (fun h0 : term153 A K => @lem4482916 A B K k s t h0 h1). Qed.
Lemma lem4482918 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term167 A B K.
Proof. exact (fun h0 : term155 A K => @lem4482917 A B K k s t h1). Qed.
Lemma lem4482919 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term169 A B K k s t.
Proof. exact (fun h0 : term152 A K k s t => @lem4482918 A B K k s t h0). Qed.
Lemma lem4482924 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : term173 A B K s t.
Proof. exact (fun k : K -> Prop => @lem4482919 A B K k s t). Qed.
Lemma lem4482929 {A B K : Type'} (t : type1470 A K) : term177 A B K t.
Proof. exact (fun s : type1470 A K => @lem4482924 A B K s t). Qed.
Lemma lem4482934 {A B K : Type'} : term181 A B K.
Proof. exact (fun t : type1470 A K => @lem4482929 A B K t). Qed.
Lemma lem4482935 {A B K : Type'} : term180 A B K.
Proof. exact (EQ_MP (@lem4476831 A B K) (@lem4482934 A B K)). Qed.
Lemma lem4482936 {A B K : Type'} (t : type1470 A K) : term796 A B K t.
Proof. exact (@lem4482935 A B K t). Qed.
Lemma lem4482937 {A B K : Type'} (t : type1470 A K) : (term796 A B K t) = (term176 A B K t).
Proof. exact (eq_refl (term796 A B K t)). Qed.
Lemma lem4482938 {A B K : Type'} (t : type1470 A K) : term176 A B K t.
Proof. exact (EQ_MP (@lem4482937 A B K t) (@lem4482936 A B K t)). Qed.
Lemma lem4482939 {A B K : Type'} (t : type1470 A K) (s : type1470 A K) : term797 A B K t s.
Proof. exact (@lem4482938 A B K t s). Qed.
Lemma lem4482940 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : (term797 A B K t s) = (term172 A B K s t).
Proof. exact (eq_refl (term797 A B K t s)). Qed.
Lemma lem4482941 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) : term172 A B K s t.
Proof. exact (EQ_MP (@lem4482940 A B K s t) (@lem4482939 A B K t s)). Qed.
Lemma lem4482942 {A B K : Type'} (s : type1470 A K) (t : type1470 A K) (k : K -> Prop) : term798 A B K s t k.
Proof. exact (@lem4482941 A B K s t k). Qed.
Lemma lem4482943 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term798 A B K s t k) = (term156 A B K k s t).
Proof. exact (eq_refl (term798 A B K s t k)). Qed.
Lemma lem4482944 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term156 A B K k s t.
Proof. exact (EQ_MP (@lem4482943 A B K k s t) (@lem4482942 A B K s t k)). Qed.
Lemma lem4482946 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term156 A B K k s t.
Proof. exact (@lem4476236 A B K k s t (@lem4482944 A B K k s t)). Qed.
Lemma lem4482947 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term166 A B K.
Proof. exact (@lem4482946 A B K k s t (@lem4476216 A K k s t h1)). Qed.
Lemma lem4482948 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term163 A B K.
Proof. exact (@lem4482947 A B K k s t h1 (@lem4476220 A K)). Qed.
Lemma lem4482949 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : term160 A B K.
Proof. exact (@lem4482948 A B K k s t h1 (@lem4476217 A K)). Qed.
Lemma lem4482950 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : False.
Proof. exact (@lem4482949 A Prop K k s t h1 (@lem4476219 A Prop K)). Qed.
Lemma lem4482951 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : (term152 A K k s t) = False.
Proof. exact (prop_ext (fun h2 : term152 A K k s t => @lem4482950 A K k s t h1) (fun h2 : False => @lem4476216 A K k s t h1)). Qed.
Lemma lem4482952 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term152 A K k s t) : False.
Proof. exact (EQ_MP (@lem4482951 A K k s t h1) (@lem4476216 A K k s t h1)). Qed.
Lemma lem4482953 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term151 A K k s t.
Proof. exact (fun h0 : term152 A K k s t => @lem4482952 A K k s t h0). Qed.
Lemma lem4482954 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term149 A K k s t.
Proof. exact (EQ_MP (@lem4476215 A K k s t) (@lem4482953 A K k s t)). Qed.
Lemma lem4482955 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term29 A K s k t) = (term30 A K k s t).
Proof. exact (EQ_MP (@lem4476211 A K k s t) (@lem4482954 A K k s t)). Qed.
Lemma lem4482960 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term799 A K k s.
Proof. exact (fun t : type1470 A K => @lem4482955 A K k s t). Qed.
Lemma lem4482965 {A K : Type'} (k : K -> Prop) : term800 A K k.
Proof. exact (fun s : type1470 A K => @lem4482960 A K k s). Qed.
Lemma lem4482970 {A K : Type'} : term801 A K.
Proof. exact (fun k : K -> Prop => @lem4482965 A K k). Qed.
