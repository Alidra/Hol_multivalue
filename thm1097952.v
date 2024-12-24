Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1097952_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1097846 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term0 A LAST'.
Proof. exact (h1). Qed.
Lemma lem1097847 {A : Type'} (h : A) (LAST' : type1141 A) (h1 : term0 A LAST') : term1 A LAST' h.
Proof. exact (@lem1097846 A LAST' h1 h). Qed.
Lemma lem1097848 {A : Type'} (h : A) (LAST' : type1141 A) : (term1 A LAST' h) = (term2 A h LAST').
Proof. exact (eq_refl (term1 A LAST' h)). Qed.
Lemma lem1097849 {A : Type'} (h : A) (LAST' : type1141 A) (h1 : term0 A LAST') : term2 A h LAST'.
Proof. exact (EQ_MP (@lem1097848 A h LAST') (@lem1097847 A h LAST' h1)). Qed.
Lemma lem1097850 {A : Type'} (h : A) (t : list A) (LAST' : type1141 A) (h1 : term0 A LAST') : term3 A h LAST' t.
Proof. exact (@lem1097849 A h LAST' h1 t). Qed.
Lemma lem1097851 {A : Type'} (h : A) (LAST' : type1141 A) (t : list A) : (term3 A h LAST' t) = ((term4 A LAST' h t) = (term5 A h LAST' t)).
Proof. exact (eq_refl (term3 A h LAST' t)). Qed.
Lemma lem1097852 {A : Type'} (h : A) (t : list A) (LAST' : type1141 A) (h1 : term0 A LAST') : (term4 A LAST' h t) = (term5 A h LAST' t).
Proof. exact (EQ_MP (@lem1097851 A h LAST' t) (@lem1097850 A h t LAST' h1)). Qed.
Lemma lem1097853 {A : Type'} (h : A) (LAST' : type1141 A) (h1 : term0 A LAST') : term2 A h LAST'.
Proof. exact (fun t : list A => @lem1097852 A h t LAST' h1). Qed.
Lemma lem1097854 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term0 A LAST'.
Proof. exact (fun h : A => @lem1097853 A h LAST' h1). Qed.
Lemma lem1097855 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term0 A LAST'.
Proof. exact (h1). Qed.
Lemma lem1097856 {A : Type'} (LAST' : type1141 A) : (term0 A LAST') = (term0 A LAST').
Proof. exact (prop_ext (fun h1 : term0 A LAST' => @lem1097854 A LAST' h1) (fun h1 : term0 A LAST' => @lem1097855 A LAST' h1)). Qed.
Lemma lem1097857 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term0 A LAST'.
Proof. exact (EQ_MP (@lem1097856 A LAST') (@lem1097855 A LAST' h1)). Qed.
Lemma lem1097858 {A Z : Type'} (NIL' : Z) : term6 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1097859 {A Z : Type'} (NIL' : Z) : (term6 A Z NIL') = (term7 A Z NIL').
Proof. exact (eq_refl (term6 A Z NIL')). Qed.
Lemma lem1097860 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (EQ_MP (@lem1097859 A Z NIL') (@lem1097858 A Z NIL')). Qed.
Lemma lem1097861 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term8 A Z NIL' CONS'.
Proof. exact (@lem1097860 A Z NIL' CONS'). Qed.
Lemma lem1097862 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term8 A Z NIL' CONS') = (term9 A Z NIL' CONS').
Proof. exact (eq_refl (term8 A Z NIL' CONS')). Qed.
Lemma lem1097863 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1097862 A Z NIL' CONS') (@lem1097861 A Z NIL' CONS')). Qed.
Lemma lem1097864 {A : Type'} (NIL' : A) (CONS' : type1393 A) : term10 A NIL' CONS'.
Proof. exact (@lem1097863 A A NIL' CONS'). Qed.
Lemma lem1097865 {A : Type'} (NIL' : A) : term11 A NIL'.
Proof. exact (@lem1097864 A NIL' (term12 A)). Qed.
Lemma lem1097866 {A : Type'} (a0 : A) : (term13 A a0) = (term14 A a0).
Proof. exact (eq_refl (term13 A a0)). Qed.
Lemma lem1097867 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1097868 {A : Type'} (a0 : A) (a1 : list A) : (term15 A a0 a1) = (term16 A a0 a1).
Proof. exact (MK_COMB (@lem1097866 A a0) (@lem1097867 A a1)). Qed.
Lemma lem1097869 {A : Type'} (a1 : list A) (a0 : A) : (term16 A a0 a1) = (term17 A a1 a0).
Proof. exact (eq_refl (term16 A a0 a1)). Qed.
Lemma lem1097870 {A : Type'} (a1 : list A) (a0 : A) : (term15 A a0 a1) = (term17 A a1 a0).
Proof. exact (TRANS (@lem1097868 A a0 a1) (@lem1097869 A a1 a0)). Qed.
Lemma lem1097871 {A : Type'} (fn : type1141 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1097872 {A : Type'} (a0 : A) (fn : type1141 A) (a1 : list A) : (term18 A a0 fn a1) = (term19 A a0 fn a1).
Proof. exact (MK_COMB (@lem1097870 A a1 a0) (@lem1097871 A fn a1)). Qed.
Lemma lem1097873 {A : Type'} (a0 : A) (fn : type1141 A) (a1 : list A) : (term19 A a0 fn a1) = (term5 A a0 fn a1).
Proof. exact (eq_refl (term19 A a0 fn a1)). Qed.
Lemma lem1097874 {A : Type'} (a0 : A) (fn : type1141 A) (a1 : list A) : (term18 A a0 fn a1) = (term5 A a0 fn a1).
Proof. exact (TRANS (@lem1097872 A a0 fn a1) (@lem1097873 A a0 fn a1)). Qed.
Lemma lem1097875 {A : Type'} (fn : type1141 A) (a0 : A) (a1 : list A) : (term20 A fn a0 a1) = (term20 A fn a0 a1).
Proof. exact (eq_refl (term20 A fn a0 a1)). Qed.
Lemma lem1097876 {A : Type'} (a0 : A) (fn : type1141 A) (a1 : list A) : ((term4 A fn a0 a1) = (term18 A a0 fn a1)) = ((term4 A fn a0 a1) = (term5 A a0 fn a1)).
Proof. exact (MK_COMB (@lem1097875 A fn a0 a1) (@lem1097874 A a0 fn a1)). Qed.
Lemma lem1097877 {A : Type'} (a0 : A) (fn : type1141 A) : (term21 A a0 fn) = (term22 A a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem1097876 A a0 fn a1)). Qed.
Lemma lem1097878 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1097879 {A : Type'} (a0 : A) (fn : type1141 A) : (term23 A a0 fn) = (term2 A a0 fn).
Proof. exact (MK_COMB (@lem1097878 A) (@lem1097877 A a0 fn)). Qed.
Lemma lem1097880 {A : Type'} (fn : type1141 A) : (term24 A fn) = (term25 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1097879 A a0 fn)). Qed.
Lemma lem1097881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1097882 {A : Type'} (fn : type1141 A) : (term26 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1097881 A) (@lem1097880 A fn)). Qed.
Lemma lem1097883 {A : Type'} (fn : type1141 A) (NIL' : A) : (term27 A fn NIL') = (term27 A fn NIL').
Proof. exact (eq_refl (term27 A fn NIL')). Qed.
Lemma lem1097884 {A : Type'} (NIL' : A) (fn : type1141 A) : (term28 A NIL' fn) = (term29 A NIL' fn).
Proof. exact (MK_COMB (@lem1097883 A fn NIL') (@lem1097882 A fn)). Qed.
Lemma lem1097885 {A : Type'} (NIL' : A) : (term30 A NIL') = (term31 A NIL').
Proof. exact (fun_ext (fun fn : type1141 A => @lem1097884 A NIL' fn)). Qed.
Lemma lem1097886 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1097887 {A : Type'} (NIL' : A) : (term11 A NIL') = (term32 A NIL').
Proof. exact (MK_COMB (@lem1097886 A) (@lem1097885 A NIL')). Qed.
Lemma lem1097888 {A : Type'} (NIL' : A) : term32 A NIL'.
Proof. exact (EQ_MP (@lem1097887 A NIL') (@lem1097865 A NIL')). Qed.
Lemma lem1097889 {A : Type'} (NIL' : A) (LAST' : type1141 A) (h1 : term29 A NIL' LAST') : term29 A NIL' LAST'.
Proof. exact (h1). Qed.
Lemma lem1097890 {A : Type'} (NIL' : A) (LAST' : type1141 A) (h1 : term29 A NIL' LAST') : term0 A LAST'.
Proof. exact (proj2 (@lem1097889 A NIL' LAST' h1)). Qed.
Lemma lem1097892 {A : Type'} (NIL' : A) (LAST' : type1141 A) (h1 : term29 A NIL' LAST') : term33 A.
Proof. exact (ex_intro (term34 A) LAST' (@lem1097890 A NIL' LAST' h1)). Qed.
Lemma lem1097893 {A : Type'} (NIL' : A) (h1 : term32 A NIL') : term32 A NIL'.
Proof. exact (h1). Qed.
Lemma lem1097894 {A : Type'} (NIL' : A) (h1 : term32 A NIL') : term33 A.
Proof. exact (ex_elim (@lem1097893 A NIL' h1) (fun LAST' : type1141 A => fun h0 : term31 A NIL' LAST' => @lem1097892 A NIL' LAST' h0)). Qed.
Lemma lem1097895 {A : Type'} (NIL' : A) : (term32 A NIL') = (term33 A).
Proof. exact (prop_ext (fun h1 : term32 A NIL' => @lem1097894 A NIL' h1) (fun h1 : term33 A => @lem1097888 A NIL')). Qed.
Lemma lem1097896 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem1097895 A (@el A)) (@lem1097888 A (@el A))). Qed.
Lemma lem1097897 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term33 A.
Proof. exact (ex_intro (term34 A) LAST' (@lem1097857 A LAST' h1)). Qed.
Lemma lem1097898 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem1097899 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (ex_elim (@lem1097898 A h1) (fun LAST' : type1141 A => fun h0 : term34 A LAST' => @lem1097897 A LAST' h0)). Qed.
Lemma lem1097900 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (prop_ext (fun h1 : term33 A => @lem1097899 A h1) (fun h1 : term33 A => @lem1097896 A)). Qed.
Lemma lem1097901 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem1097900 A) (@lem1097896 A)). Qed.
Lemma lem1097904 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term0 A LAST'.
Proof. exact (h1). Qed.
Lemma lem1097905 {A : Type'} (LAST' : type1141 A) (h1 : term0 A LAST') : term33 A.
Proof. exact (ex_intro (term34 A) LAST' (@lem1097904 A LAST' h1)). Qed.
Lemma lem1097906 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem1097907 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (ex_elim (@lem1097906 A h1) (fun LAST' : type1141 A => fun h0 : term34 A LAST' => @lem1097905 A LAST' h0)). Qed.
Lemma lem1097908 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (prop_ext (fun h1 : term33 A => @lem1097907 A h1) (fun h1 : term33 A => @lem1097901 A)). Qed.
Lemma lem1097909 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem1097908 A) (@lem1097901 A)). Qed.
Lemma lem1097910 {A : Type'} : term35 A.
Proof. exact (fun _17954 : type1673 => @lem1097909 A). Qed.
Lemma lem1097911 {A B : Type'} (P : type1413 A B) : term36 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1097912 {A B : Type'} (P : type1413 A B) : (term36 A B P) = ((term37 A B P) = (term38 A B P)).
Proof. exact (eq_refl (term36 A B P)). Qed.
Lemma lem1097915 {A B : Type'} (P : type1413 A B) : (term37 A B P) = (term38 A B P).
Proof. exact (EQ_MP (@lem1097912 A B P) (@lem1097911 A B P)). Qed.
Lemma lem1097916 {A : Type'} (P : type1283 A) : (term39 A P) = (term40 A P).
Proof. exact (@lem1097915 type1673 (type1141 A) P). Qed.
Lemma lem1097917 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (@lem1097916 A (term43 A)). Qed.
Lemma lem1097918 {A : Type'} (_17954 : type1673) : (term44 A _17954) = (term34 A).
Proof. exact (eq_refl (term44 A _17954)). Qed.
Lemma lem1097919 {A : Type'} (LAST' : type1141 A) : LAST' = LAST'.
Proof. exact (eq_refl LAST'). Qed.
Lemma lem1097920 {A : Type'} (_17954 : type1673) (LAST' : type1141 A) : (term45 A _17954 LAST') = (term46 A LAST').
Proof. exact (MK_COMB (@lem1097918 A _17954) (@lem1097919 A LAST')). Qed.
Lemma lem1097921 {A : Type'} (LAST' : type1141 A) : (term46 A LAST') = (term0 A LAST').
Proof. exact (eq_refl (term46 A LAST')). Qed.
Lemma lem1097922 {A : Type'} (_17954 : type1673) (LAST' : type1141 A) : (term45 A _17954 LAST') = (term0 A LAST').
Proof. exact (TRANS (@lem1097920 A _17954 LAST') (@lem1097921 A LAST')). Qed.
Lemma lem1097923 {A : Type'} (_17954 : type1673) : (term47 A _17954) = (term34 A).
Proof. exact (fun_ext (fun LAST' : type1141 A => @lem1097922 A _17954 LAST')). Qed.
Lemma lem1097924 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1097925 {A : Type'} (_17954 : type1673) : (term48 A _17954) = (term33 A).
Proof. exact (MK_COMB (@lem1097924 A) (@lem1097923 A _17954)). Qed.
Lemma lem1097926 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (fun_ext (fun _17954 : type1673 => @lem1097925 A _17954)). Qed.
Lemma lem1097927 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1097928 {A : Type'} : (term41 A) = (term35 A).
Proof. exact (MK_COMB (@lem1097927) (@lem1097926 A)). Qed.
Lemma lem1097929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1097930 {A : Type'} : (term51 A) = (term52 A).
Proof. exact (MK_COMB (@lem1097929) (@lem1097928 A)). Qed.
Lemma lem1097931 {A : Type'} (_17954 : type1673) : (term44 A _17954) = (term34 A).
Proof. exact (eq_refl (term44 A _17954)). Qed.
Lemma lem1097932 {A : Type'} (LAST' : type1289 A) (_17954 : type1673) : (LAST' _17954) = (LAST' _17954).
Proof. exact (eq_refl (LAST' _17954)). Qed.
Lemma lem1097933 {A : Type'} (LAST' : type1289 A) (_17954 : type1673) : (term53 A LAST' _17954) = (term54 A LAST' _17954).
Proof. exact (MK_COMB (@lem1097931 A _17954) (@lem1097932 A LAST' _17954)). Qed.
Lemma lem1097934 {A : Type'} (LAST' : type1289 A) (_17954 : type1673) : (term54 A LAST' _17954) = (term55 A LAST' _17954).
Proof. exact (eq_refl (term54 A LAST' _17954)). Qed.
Lemma lem1097935 {A : Type'} (LAST' : type1289 A) (_17954 : type1673) : (term53 A LAST' _17954) = (term55 A LAST' _17954).
Proof. exact (TRANS (@lem1097933 A LAST' _17954) (@lem1097934 A LAST' _17954)). Qed.
Lemma lem1097936 {A : Type'} (LAST' : type1289 A) : (term56 A LAST') = (term57 A LAST').
Proof. exact (fun_ext (fun _17954 : type1673 => @lem1097935 A LAST' _17954)). Qed.
Lemma lem1097937 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1097938 {A : Type'} (LAST' : type1289 A) : (term58 A LAST') = (term59 A LAST').
Proof. exact (MK_COMB (@lem1097937) (@lem1097936 A LAST')). Qed.
Lemma lem1097939 {A : Type'} : (term60 A) = (term61 A).
Proof. exact (fun_ext (fun LAST' : type1289 A => @lem1097938 A LAST')). Qed.
Lemma lem1097940 {A : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (list A) -> A)) = (@ex ((prod nat (prod nat (prod nat nat))) -> (list A) -> A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> (list A) -> A))). Qed.
Lemma lem1097941 {A : Type'} : (term42 A) = (term62 A).
Proof. exact (MK_COMB (@lem1097940 A) (@lem1097939 A)). Qed.
Lemma lem1097942 {A : Type'} : ((term41 A) = (term42 A)) = ((term35 A) = (term62 A)).
Proof. exact (MK_COMB (@lem1097930 A) (@lem1097941 A)). Qed.
Lemma lem1097943 {A : Type'} : (term35 A) = (term62 A).
Proof. exact (EQ_MP (@lem1097942 A) (@lem1097917 A)). Qed.
Lemma lem1097944 {A : Type'} : term62 A.
Proof. exact (EQ_MP (@lem1097943 A) (@lem1097910 A)). Qed.
Lemma lem1097946 {A : Type'} : (@ex A) = (term63 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1097947 {A : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (list A) -> A)) = (term64 A).
Proof. exact (@lem1097946 (type1289 A)). Qed.
Lemma lem1097948 {A : Type'} : (term61 A) = (term61 A).
Proof. exact (eq_refl (term61 A)). Qed.
Lemma lem1097949 {A : Type'} : (term62 A) = (term65 A).
Proof. exact (MK_COMB (@lem1097947 A) (@lem1097948 A)). Qed.
Lemma lem1097950 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (eq_refl (term65 A)). Qed.
Lemma lem1097951 {A : Type'} : (term62 A) = (term66 A).
Proof. exact (TRANS (@lem1097949 A) (@lem1097950 A)). Qed.
Lemma lem1097952 {A : Type'} : term66 A.
Proof. exact (EQ_MP (@lem1097951 A) (@lem1097944 A)). Qed.
