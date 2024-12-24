Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm77014_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem76898 (add' : type1606) (h1 : (term0 add') = term1) : (term0 add') = term1.
Proof. exact (h1). Qed.
Lemma lem76899 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76900 (n : nat) (add' : type1606) (h1 : (term0 add') = term1) : (term2 add' n) = (term3 n).
Proof. exact (MK_COMB (@lem76898 add' h1) (@lem76899 n)). Qed.
Lemma lem76901 (n : nat) : (term3 n) = n.
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem76902 (add' : type1606) (n : nat) : (term4 add' n) = (term4 add' n).
Proof. exact (eq_refl (term4 add' n)). Qed.
Lemma lem76903 (add' : type1606) (n : nat) : ((term2 add' n) = (term3 n)) = ((term2 add' n) = n).
Proof. exact (MK_COMB (@lem76902 add' n) (@lem76901 n)). Qed.
Lemma lem76904 (n : nat) (add' : type1606) (h1 : (term0 add') = term1) : (term2 add' n) = n.
Proof. exact (EQ_MP (@lem76903 add' n) (@lem76900 n add' h1)). Qed.
Lemma lem76905 (add' : type1606) (h1 : (term0 add') = term1) : term5 add'.
Proof. exact (fun n : nat => @lem76904 n add' h1). Qed.
Lemma lem76906 (add' : type1606) (h1 : term6 add') : term6 add'.
Proof. exact (h1). Qed.
Lemma lem76907 (m : nat) (add' : type1606) (h1 : term6 add') : term7 add' m.
Proof. exact (@lem76906 add' h1 m). Qed.
Lemma lem76908 (add' : type1606) (m : nat) : (term7 add' m) = ((term8 add' m) = (term9 add' m)).
Proof. exact (eq_refl (term7 add' m)). Qed.
Lemma lem76909 (m : nat) (add' : type1606) (h1 : term6 add') : (term8 add' m) = (term9 add' m).
Proof. exact (EQ_MP (@lem76908 add' m) (@lem76907 m add' h1)). Qed.
Lemma lem76910 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76911 (m : nat) (n : nat) (add' : type1606) (h1 : term6 add') : (term10 add' m n) = (term11 add' m n).
Proof. exact (MK_COMB (@lem76909 m add' h1) (@lem76910 n)). Qed.
Lemma lem76912 (add' : type1606) (m : nat) (n : nat) : (term11 add' m n) = (term12 add' m n).
Proof. exact (eq_refl (term11 add' m n)). Qed.
Lemma lem76913 (add' : type1606) (m : nat) (n : nat) : (term13 add' m n) = (term13 add' m n).
Proof. exact (eq_refl (term13 add' m n)). Qed.
Lemma lem76914 (add' : type1606) (m : nat) (n : nat) : ((term10 add' m n) = (term11 add' m n)) = ((term10 add' m n) = (term12 add' m n)).
Proof. exact (MK_COMB (@lem76913 add' m n) (@lem76912 add' m n)). Qed.
Lemma lem76915 (m : nat) (n : nat) (add' : type1606) (h1 : term6 add') : (term10 add' m n) = (term12 add' m n).
Proof. exact (EQ_MP (@lem76914 add' m n) (@lem76911 m n add' h1)). Qed.
Lemma lem76916 (m : nat) (add' : type1606) (h1 : term6 add') : term14 add' m.
Proof. exact (fun n : nat => @lem76915 m n add' h1). Qed.
Lemma lem76917 (add' : type1606) (h1 : term6 add') : term15 add'.
Proof. exact (fun m : nat => @lem76916 m add' h1). Qed.
Lemma lem76918 (add' : type1606) (h1 : term16 add') : term16 add'.
Proof. exact (h1). Qed.
Lemma lem76919 (add' : type1606) (h1 : term16 add') : term6 add'.
Proof. exact (proj2 (@lem76918 add' h1)). Qed.
Lemma lem76920 (add' : type1606) (h1 : term16 add') : (term0 add') = term1.
Proof. exact (proj1 (@lem76918 add' h1)). Qed.
Lemma lem76921 (add' : type1606) (h1 : term16 add') : ((term0 add') = term1) = (term5 add').
Proof. exact (prop_ext (fun h2 : (term0 add') = term1 => @lem76905 add' h2) (fun h2 : term5 add' => @lem76920 add' h1)). Qed.
Lemma lem76922 (add' : type1606) (h1 : term16 add') : term5 add'.
Proof. exact (EQ_MP (@lem76921 add' h1) (@lem76920 add' h1)). Qed.
Lemma lem76923 (add' : type1606) (h1 : term16 add') : (term6 add') = (term15 add').
Proof. exact (prop_ext (fun h2 : term6 add' => @lem76917 add' h2) (fun h2 : term15 add' => @lem76919 add' h1)). Qed.
Lemma lem76924 (add' : type1606) (h1 : term16 add') : term15 add'.
Proof. exact (EQ_MP (@lem76923 add' h1) (@lem76919 add' h1)). Qed.
Lemma lem76925 (add' : type1606) (h1 : term16 add') : term17 add'.
Proof. exact (conj (@lem76922 add' h1) (@lem76924 add' h1)). Qed.
Lemma lem76926 {A : Type'} (e : A) : term18 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem76927 {A : Type'} (e : A) : (term18 A e) = (term19 A e).
Proof. exact (eq_refl (term18 A e)). Qed.
Lemma lem76928 {A : Type'} (e : A) : term19 A e.
Proof. exact (EQ_MP (@lem76927 A e) (@lem76926 A e)). Qed.
Lemma lem76929 {A : Type'} (e : A) (f : type1423 A) : term20 A e f.
Proof. exact (@lem76928 A e f). Qed.
Lemma lem76930 {A : Type'} (e : A) (f : type1423 A) : (term20 A e f) = (term21 A e f).
Proof. exact (eq_refl (term20 A e f)). Qed.
Lemma lem76931 {A : Type'} (e : A) (f : type1423 A) : term21 A e f.
Proof. exact (EQ_MP (@lem76930 A e f) (@lem76929 A e f)). Qed.
Lemma lem76932 (e : nat -> nat) (f : type1000) : term22 e f.
Proof. exact (@lem76931 (nat -> nat) e f). Qed.
Lemma lem76933 : term23.
Proof. exact (@lem76932 term1 term24). Qed.
Lemma lem76934 (fn : type1606) (n : nat) : (term25 fn n) = (term26 fn n).
Proof. exact (eq_refl (term25 fn n)). Qed.
Lemma lem76935 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76936 (fn : type1606) (n : nat) : (term27 fn n) = (term28 fn n).
Proof. exact (MK_COMB (@lem76934 fn n) (@lem76935 n)). Qed.
Lemma lem76937 (fn : type1606) (n : nat) : (term28 fn n) = (term9 fn n).
Proof. exact (eq_refl (term28 fn n)). Qed.
Lemma lem76938 (fn : type1606) (n : nat) : (term27 fn n) = (term9 fn n).
Proof. exact (TRANS (@lem76936 fn n) (@lem76937 fn n)). Qed.
Lemma lem76939 (fn : type1606) (n : nat) : (term29 fn n) = (term29 fn n).
Proof. exact (eq_refl (term29 fn n)). Qed.
Lemma lem76940 (fn : type1606) (n : nat) : ((term8 fn n) = (term27 fn n)) = ((term8 fn n) = (term9 fn n)).
Proof. exact (MK_COMB (@lem76939 fn n) (@lem76938 fn n)). Qed.
Lemma lem76941 (fn : type1606) : (term30 fn) = (term31 fn).
Proof. exact (fun_ext (fun n : nat => @lem76940 fn n)). Qed.
Lemma lem76942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76943 (fn : type1606) : (term32 fn) = (term6 fn).
Proof. exact (MK_COMB (@lem76942) (@lem76941 fn)). Qed.
Lemma lem76944 (fn : type1606) : (term33 fn) = (term33 fn).
Proof. exact (eq_refl (term33 fn)). Qed.
Lemma lem76945 (fn : type1606) : (term34 fn) = (term16 fn).
Proof. exact (MK_COMB (@lem76944 fn) (@lem76943 fn)). Qed.
Lemma lem76946 : term35 = term36.
Proof. exact (fun_ext (fun fn : type1606 => @lem76945 fn)). Qed.
Lemma lem76947 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem76948 : term23 = term37.
Proof. exact (MK_COMB (@lem76947) (@lem76946)). Qed.
Lemma lem76949 : term37.
Proof. exact (EQ_MP (@lem76948) (@lem76933)). Qed.
Lemma lem76950 (add' : type1606) (h1 : term16 add') : term16 add'.
Proof. exact (h1). Qed.
Lemma lem76951 (add' : type1606) (h1 : term16 add') : term6 add'.
Proof. exact (proj2 (@lem76950 add' h1)). Qed.
Lemma lem76952 (add' : type1606) (h1 : term16 add') : (term0 add') = term1.
Proof. exact (proj1 (@lem76950 add' h1)). Qed.
Lemma lem76953 (add' : type1606) (h1 : term16 add') : term16 add'.
Proof. exact (conj (@lem76952 add' h1) (@lem76951 add' h1)). Qed.
Lemma lem76954 (add' : type1606) (h1 : term16 add') : term37.
Proof. exact (ex_intro term36 add' (@lem76953 add' h1)). Qed.
Lemma lem76955 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem76956 (h1 : term37) : term37.
Proof. exact (ex_elim (@lem76955 h1) (fun add' : type1606 => fun h0 : term36 add' => @lem76954 add' h0)). Qed.
Lemma lem76957 : term37 = term37.
Proof. exact (prop_ext (fun h1 : term37 => @lem76956 h1) (fun h1 : term37 => @lem76949)). Qed.
Lemma lem76958 : term37.
Proof. exact (EQ_MP (@lem76957) (@lem76949)). Qed.
Lemma lem76959 (add' : type1606) (h1 : term16 add') : term38.
Proof. exact (ex_intro term39 add' (@lem76925 add' h1)). Qed.
Lemma lem76960 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem76961 (h1 : term37) : term38.
Proof. exact (ex_elim (@lem76960 h1) (fun add' : type1606 => fun h0 : term36 add' => @lem76959 add' h0)). Qed.
Lemma lem76962 : term37 = term38.
Proof. exact (prop_ext (fun h1 : term37 => @lem76961 h1) (fun h1 : term38 => @lem76958)). Qed.
Lemma lem76963 : term38.
Proof. exact (EQ_MP (@lem76962) (@lem76958)). Qed.
Lemma lem76966 (add' : type1606) (h1 : term17 add') : term17 add'.
Proof. exact (h1). Qed.
Lemma lem76967 (add' : type1606) (h1 : term17 add') : term38.
Proof. exact (ex_intro term39 add' (@lem76966 add' h1)). Qed.
Lemma lem76968 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem76969 (h1 : term38) : term38.
Proof. exact (ex_elim (@lem76968 h1) (fun add' : type1606 => fun h0 : term39 add' => @lem76967 add' h0)). Qed.
Lemma lem76970 : term38 = term38.
Proof. exact (prop_ext (fun h1 : term38 => @lem76969 h1) (fun h1 : term38 => @lem76963)). Qed.
Lemma lem76971 : term38.
Proof. exact (EQ_MP (@lem76970) (@lem76963)). Qed.
Lemma lem76972 : term40.
Proof. exact (fun _2155 : nat => @lem76971). Qed.
Lemma lem76973 {A B : Type'} (P : type1413 A B) : term41 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem76974 {A B : Type'} (P : type1413 A B) : (term41 A B P) = ((term42 A B P) = (term43 A B P)).
Proof. exact (eq_refl (term41 A B P)). Qed.
Lemma lem76977 {A B : Type'} (P : type1413 A B) : (term42 A B P) = (term43 A B P).
Proof. exact (EQ_MP (@lem76974 A B P) (@lem76973 A B P)). Qed.
Lemma lem76978 (P : type1581) : (term44 P) = (term45 P).
Proof. exact (@lem76977 nat type1606 P). Qed.
Lemma lem76979 : term46 = term47.
Proof. exact (@lem76978 term48). Qed.
Lemma lem76980 (_2155 : nat) : (term49 _2155) = term39.
Proof. exact (eq_refl (term49 _2155)). Qed.
Lemma lem76981 (add' : type1606) : add' = add'.
Proof. exact (eq_refl add'). Qed.
Lemma lem76982 (_2155 : nat) (add' : type1606) : (term50 _2155 add') = (term51 add').
Proof. exact (MK_COMB (@lem76980 _2155) (@lem76981 add')). Qed.
Lemma lem76983 (add' : type1606) : (term51 add') = (term17 add').
Proof. exact (eq_refl (term51 add')). Qed.
Lemma lem76984 (_2155 : nat) (add' : type1606) : (term50 _2155 add') = (term17 add').
Proof. exact (TRANS (@lem76982 _2155 add') (@lem76983 add')). Qed.
Lemma lem76985 (_2155 : nat) : (term52 _2155) = term39.
Proof. exact (fun_ext (fun add' : type1606 => @lem76984 _2155 add')). Qed.
Lemma lem76986 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem76987 (_2155 : nat) : (term53 _2155) = term38.
Proof. exact (MK_COMB (@lem76986) (@lem76985 _2155)). Qed.
Lemma lem76988 : term54 = term55.
Proof. exact (fun_ext (fun _2155 : nat => @lem76987 _2155)). Qed.
Lemma lem76989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76990 : term46 = term40.
Proof. exact (MK_COMB (@lem76989) (@lem76988)). Qed.
Lemma lem76991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem76992 : term56 = term57.
Proof. exact (MK_COMB (@lem76991) (@lem76990)). Qed.
Lemma lem76993 (_2155 : nat) : (term49 _2155) = term39.
Proof. exact (eq_refl (term49 _2155)). Qed.
Lemma lem76994 (add' : type1602) (_2155 : nat) : (add' _2155) = (add' _2155).
Proof. exact (eq_refl (add' _2155)). Qed.
Lemma lem76995 (add' : type1602) (_2155 : nat) : (term58 add' _2155) = (term59 add' _2155).
Proof. exact (MK_COMB (@lem76993 _2155) (@lem76994 add' _2155)). Qed.
Lemma lem76996 (add' : type1602) (_2155 : nat) : (term59 add' _2155) = (term60 add' _2155).
Proof. exact (eq_refl (term59 add' _2155)). Qed.
Lemma lem76997 (add' : type1602) (_2155 : nat) : (term58 add' _2155) = (term60 add' _2155).
Proof. exact (TRANS (@lem76995 add' _2155) (@lem76996 add' _2155)). Qed.
Lemma lem76998 (add' : type1602) : (term61 add') = (term62 add').
Proof. exact (fun_ext (fun _2155 : nat => @lem76997 add' _2155)). Qed.
Lemma lem76999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77000 (add' : type1602) : (term63 add') = (term64 add').
Proof. exact (MK_COMB (@lem76999) (@lem76998 add')). Qed.
Lemma lem77001 : term65 = term66.
Proof. exact (fun_ext (fun add' : type1602 => @lem77000 add')). Qed.
Lemma lem77002 : (@ex (nat -> nat -> nat -> nat)) = (@ex (nat -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> nat))). Qed.
Lemma lem77003 : term47 = term67.
Proof. exact (MK_COMB (@lem77002) (@lem77001)). Qed.
Lemma lem77004 : (term46 = term47) = (term40 = term67).
Proof. exact (MK_COMB (@lem76992) (@lem77003)). Qed.
Lemma lem77005 : term40 = term67.
Proof. exact (EQ_MP (@lem77004) (@lem76979)). Qed.
Lemma lem77006 : term67.
Proof. exact (EQ_MP (@lem77005) (@lem76972)). Qed.
Lemma lem77008 {A : Type'} : (@ex A) = (term68 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem77009 : (@ex (nat -> nat -> nat -> nat)) = term69.
Proof. exact (@lem77008 type1602). Qed.
Lemma lem77010 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem77011 : term67 = term70.
Proof. exact (MK_COMB (@lem77009) (@lem77010)). Qed.
Lemma lem77012 : term70 = term71.
Proof. exact (eq_refl term70). Qed.
Lemma lem77013 : term67 = term71.
Proof. exact (TRANS (@lem77011) (@lem77012)). Qed.
Lemma lem77014 : term71.
Proof. exact (EQ_MP (@lem77013) (@lem77006)). Qed.
