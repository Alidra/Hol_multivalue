Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_EMPTY_term_abbrevs.
Require Import PCROSS_EQ_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8005885 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : term0 _141954 _141955 _141956 s.
Proof. exact (@lem8005884 _141954 _141955 _141956 s). Qed.
Lemma lem8005886 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term0 _141954 _141955 _141956 s) = (term1 _141954 _141955 _141956 s).
Proof. exact (eq_refl (term0 _141954 _141955 _141956 s)). Qed.
Lemma lem8005887 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : term1 _141954 _141955 _141956 s.
Proof. exact (EQ_MP (@lem8005886 _141954 _141955 _141956 s) (@lem8005885 _141954 _141955 _141956 s)). Qed.
Lemma lem8005888 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : term2 _141954 _141955 _141956 s t.
Proof. exact (@lem8005887 _141954 _141955 _141956 s t). Qed.
Lemma lem8005889 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term2 _141954 _141955 _141956 s t) = (((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term3 _141954 _141955 _141956 s t)).
Proof. exact (eq_refl (term2 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005898 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term3 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8005889 _141954 _141955 _141956 s t) (@lem8005888 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005899 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) (t : type24 _141980 _141982) : ((@PCROSS _141980 _141981 _141982 s t) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))) = (term3 _141980 _141981 _141982 s t).
Proof. exact (@lem8005898 _141980 _141981 _141982 s t). Qed.
Lemma lem8005900 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : ((@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))) = (term4 _141980 _141981 _141982 s).
Proof. exact (@lem8005899 _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))). Qed.
Lemma lem8005906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8005907 {_141980 _141982 : Type'} (x : type24 _141980 _141982) : (x = x) = True.
Proof. exact (@lem8005906 (type24 _141980 _141982) x). Qed.
Lemma lem8005908 {_141980 _141982 : Type'} : ((@EMPTY (cart _141980 _141982)) = (@EMPTY (cart _141980 _141982))) = True.
Proof. exact (@lem8005907 _141980 _141982 (@EMPTY (cart _141980 _141982))). Qed.
Lemma lem8005909 {_141980 _141981 : Type'} (s : type24 _141980 _141981) : (term5 _141980 _141981 s) = (term5 _141980 _141981 s).
Proof. exact (eq_refl (term5 _141980 _141981 s)). Qed.
Lemma lem8005910 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (term4 _141980 _141981 _141982 s) = (term6 _141980 _141981 s).
Proof. exact (MK_COMB (@lem8005909 _141980 _141981 s) (@lem8005908 _141980 _141982)). Qed.
Lemma lem8005912 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem8005913 {_141980 _141981 : Type'} (s : type24 _141980 _141981) : (term6 _141980 _141981 s) = True.
Proof. exact (@lem8005912 (s = (@EMPTY (cart _141980 _141981)))). Qed.
Lemma lem8005914 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (term4 _141980 _141981 _141982 s) = True.
Proof. exact (TRANS (@lem8005910 _141980 _141981 _141982 s) (@lem8005913 _141980 _141981 s)). Qed.
Lemma lem8005915 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : ((@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))) = True.
Proof. exact (TRANS (@lem8005900 _141980 _141981 _141982 s) (@lem8005914 _141980 _141981 _141982 s)). Qed.
Lemma lem8005916 {_141980 _141981 _141982 : Type'} : (term7 _141980 _141981 _141982) = (term8 _141980 _141981).
Proof. exact (fun_ext (fun s : type24 _141980 _141981 => @lem8005915 _141980 _141981 _141982 s)). Qed.
Lemma lem8005917 {_141980 _141981 : Type'} : (@all ((cart _141980 _141981) -> Prop)) = (@all ((cart _141980 _141981) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141980 _141981) -> Prop))). Qed.
Lemma lem8005918 {_141980 _141981 _141982 : Type'} : (term9 _141980 _141981 _141982) = (term10 _141980 _141981).
Proof. exact (MK_COMB (@lem8005917 _141980 _141981) (@lem8005916 _141980 _141981 _141982)). Qed.
Lemma lem8005920 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8005921 {_141980 _141981 : Type'} (t : Prop) : (term12 _141980 _141981 t) = t.
Proof. exact (@lem8005920 (type24 _141980 _141981) t). Qed.
Lemma lem8005922 {_141980 _141981 : Type'} : (term10 _141980 _141981) = True.
Proof. exact (@lem8005921 _141980 _141981 True). Qed.
Lemma lem8005923 {_141980 _141981 _141982 : Type'} : (term9 _141980 _141981 _141982) = True.
Proof. exact (TRANS (@lem8005918 _141980 _141981 _141982) (@lem8005922 _141980 _141981)). Qed.
Lemma lem8005924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8005925 {_141980 _141981 _141982 : Type'} : (term13 _141980 _141981 _141982) = (and True).
Proof. exact (MK_COMB (@lem8005924) (@lem8005923 _141980 _141981 _141982)). Qed.
Lemma lem8005931 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term3 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8005889 _141954 _141955 _141956 s t) (@lem8005888 _141954 _141955 _141956 s t)). Qed.
Lemma lem8005932 {_141994 _141995 _141996 : Type'} (s : type24 _141994 _141995) (t : type24 _141994 _141996) : ((@PCROSS _141994 _141995 _141996 s t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))) = (term3 _141994 _141995 _141996 s t).
Proof. exact (@lem8005931 _141994 _141995 _141996 s t). Qed.
Lemma lem8005933 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : ((@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))) = (term14 _141994 _141995 _141996 t).
Proof. exact (@lem8005932 _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t). Qed.
Lemma lem8005937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8005938 {_141994 _141995 : Type'} (x : type24 _141994 _141995) : (x = x) = True.
Proof. exact (@lem8005937 (type24 _141994 _141995) x). Qed.
Lemma lem8005939 {_141994 _141995 : Type'} : ((@EMPTY (cart _141994 _141995)) = (@EMPTY (cart _141994 _141995))) = True.
Proof. exact (@lem8005938 _141994 _141995 (@EMPTY (cart _141994 _141995))). Qed.
Lemma lem8005940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8005941 {_141994 _141995 : Type'} : (term15 _141994 _141995) = (or True).
Proof. exact (MK_COMB (@lem8005940) (@lem8005939 _141994 _141995)). Qed.
Lemma lem8005944 {_141994 _141996 : Type'} (t : type24 _141994 _141996) : (t = (@EMPTY (cart _141994 _141996))) = (t = (@EMPTY (cart _141994 _141996))).
Proof. exact (eq_refl (t = (@EMPTY (cart _141994 _141996)))). Qed.
Lemma lem8005945 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (term14 _141994 _141995 _141996 t) = (term16 _141994 _141996 t).
Proof. exact (MK_COMB (@lem8005941 _141994 _141995) (@lem8005944 _141994 _141996 t)). Qed.
Lemma lem8005947 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8005948 {_141994 _141996 : Type'} (t : type24 _141994 _141996) : (term16 _141994 _141996 t) = True.
Proof. exact (@lem8005947 (t = (@EMPTY (cart _141994 _141996)))). Qed.
Lemma lem8005949 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (term14 _141994 _141995 _141996 t) = True.
Proof. exact (TRANS (@lem8005945 _141994 _141995 _141996 t) (@lem8005948 _141994 _141996 t)). Qed.
Lemma lem8005950 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : ((@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))) = True.
Proof. exact (TRANS (@lem8005933 _141994 _141995 _141996 t) (@lem8005949 _141994 _141995 _141996 t)). Qed.
Lemma lem8005951 {_141994 _141995 _141996 : Type'} : (term17 _141994 _141995 _141996) = (term8 _141994 _141996).
Proof. exact (fun_ext (fun t : type24 _141994 _141996 => @lem8005950 _141994 _141995 _141996 t)). Qed.
Lemma lem8005952 {_141994 _141996 : Type'} : (@all ((cart _141994 _141996) -> Prop)) = (@all ((cart _141994 _141996) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141994 _141996) -> Prop))). Qed.
Lemma lem8005953 {_141994 _141995 _141996 : Type'} : (term18 _141994 _141995 _141996) = (term10 _141994 _141996).
Proof. exact (MK_COMB (@lem8005952 _141994 _141996) (@lem8005951 _141994 _141995 _141996)). Qed.
Lemma lem8005955 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8005956 {_141994 _141996 : Type'} (t : Prop) : (term12 _141994 _141996 t) = t.
Proof. exact (@lem8005955 (type24 _141994 _141996) t). Qed.
Lemma lem8005957 {_141994 _141996 : Type'} : (term10 _141994 _141996) = True.
Proof. exact (@lem8005956 _141994 _141996 True). Qed.
Lemma lem8005958 {_141994 _141995 _141996 : Type'} : (term18 _141994 _141995 _141996) = True.
Proof. exact (TRANS (@lem8005953 _141994 _141995 _141996) (@lem8005957 _141994 _141996)). Qed.
Lemma lem8005959 {_141980 _141981 _141982 _141994 _141995 _141996 : Type'} : (term19 _141980 _141981 _141982 _141994 _141995 _141996) = (True /\ True).
Proof. exact (MK_COMB (@lem8005925 _141980 _141981 _141982) (@lem8005958 _141994 _141995 _141996)). Qed.
Lemma lem8005961 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8005962 : (True /\ True) = True.
Proof. exact (@lem8005961 True). Qed.
Lemma lem8005963 {_141980 _141981 _141982 _141994 _141995 _141996 : Type'} : (term19 _141980 _141981 _141982 _141994 _141995 _141996) = True.
Proof. exact (TRANS (@lem8005959 _141980 _141981 _141982 _141994 _141995 _141996) (@lem8005962)). Qed.
Lemma lem8005964 {_141980 _141981 _141982 _141994 _141995 _141996 : Type'} : True = (term19 _141980 _141981 _141982 _141994 _141995 _141996).
Proof. exact (SYM (@lem8005963 _141980 _141981 _141982 _141994 _141995 _141996)). Qed.
Lemma lem8005965 {_141980 _141981 _141982 _141994 _141995 _141996 : Type'} : term19 _141980 _141981 _141982 _141994 _141995 _141996.
Proof. exact (EQ_MP (@lem8005964 _141980 _141981 _141982 _141994 _141995 _141996) (@lem0)). Qed.
