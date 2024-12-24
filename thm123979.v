Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm123979_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem123877 (EVEN' : nat -> Prop) (h1 : (term0 EVEN') = True) : (term0 EVEN') = True.
Proof. exact (h1). Qed.
Lemma lem123878 (EVEN' : nat -> Prop) (h1 : term1 EVEN') : term1 EVEN'.
Proof. exact (h1). Qed.
Lemma lem123879 (n : nat) (EVEN' : nat -> Prop) (h1 : term1 EVEN') : term2 EVEN' n.
Proof. exact (@lem123878 EVEN' h1 n). Qed.
Lemma lem123880 (EVEN' : nat -> Prop) (n : nat) : (term2 EVEN' n) = ((term3 EVEN' n) = (term4 EVEN' n)).
Proof. exact (eq_refl (term2 EVEN' n)). Qed.
Lemma lem123881 (n : nat) (EVEN' : nat -> Prop) (h1 : term1 EVEN') : (term3 EVEN' n) = (term4 EVEN' n).
Proof. exact (EQ_MP (@lem123880 EVEN' n) (@lem123879 n EVEN' h1)). Qed.
Lemma lem123882 (EVEN' : nat -> Prop) (h1 : term1 EVEN') : term1 EVEN'.
Proof. exact (fun n : nat => @lem123881 n EVEN' h1). Qed.
Lemma lem123883 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term5 EVEN'.
Proof. exact (h1). Qed.
Lemma lem123884 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term1 EVEN'.
Proof. exact (proj2 (@lem123883 EVEN' h1)). Qed.
Lemma lem123885 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : (term0 EVEN') = True.
Proof. exact (proj1 (@lem123883 EVEN' h1)). Qed.
Lemma lem123886 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : ((term0 EVEN') = True) = ((term0 EVEN') = True).
Proof. exact (prop_ext (fun h2 : (term0 EVEN') = True => @lem123877 EVEN' h2) (fun h2 : (term0 EVEN') = True => @lem123885 EVEN' h1)). Qed.
Lemma lem123887 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : (term0 EVEN') = True.
Proof. exact (EQ_MP (@lem123886 EVEN' h1) (@lem123885 EVEN' h1)). Qed.
Lemma lem123888 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : (term1 EVEN') = (term1 EVEN').
Proof. exact (prop_ext (fun h2 : term1 EVEN' => @lem123882 EVEN' h2) (fun h2 : term1 EVEN' => @lem123884 EVEN' h1)). Qed.
Lemma lem123889 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term1 EVEN'.
Proof. exact (EQ_MP (@lem123888 EVEN' h1) (@lem123884 EVEN' h1)). Qed.
Lemma lem123890 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term5 EVEN'.
Proof. exact (conj (@lem123887 EVEN' h1) (@lem123889 EVEN' h1)). Qed.
Lemma lem123891 {A : Type'} (e : A) : term6 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem123892 {A : Type'} (e : A) : (term6 A e) = (term7 A e).
Proof. exact (eq_refl (term6 A e)). Qed.
Lemma lem123893 {A : Type'} (e : A) : term7 A e.
Proof. exact (EQ_MP (@lem123892 A e) (@lem123891 A e)). Qed.
Lemma lem123894 {A : Type'} (e : A) (f : type1423 A) : term8 A e f.
Proof. exact (@lem123893 A e f). Qed.
Lemma lem123895 {A : Type'} (e : A) (f : type1423 A) : (term8 A e f) = (term9 A e f).
Proof. exact (eq_refl (term8 A e f)). Qed.
Lemma lem123896 {A : Type'} (e : A) (f : type1423 A) : term9 A e f.
Proof. exact (EQ_MP (@lem123895 A e f) (@lem123894 A e f)). Qed.
Lemma lem123897 (e : Prop) (f : type1544) : term10 e f.
Proof. exact (@lem123896 Prop e f). Qed.
Lemma lem123898 : term11.
Proof. exact (@lem123897 True term12). Qed.
Lemma lem123899 (fn : nat -> Prop) (n : nat) : (term13 fn n) = (term14 fn n).
Proof. exact (eq_refl (term13 fn n)). Qed.
Lemma lem123900 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem123901 (fn : nat -> Prop) (n : nat) : (term15 fn n) = (term16 fn n).
Proof. exact (MK_COMB (@lem123899 fn n) (@lem123900 n)). Qed.
Lemma lem123902 (fn : nat -> Prop) (n : nat) : (term16 fn n) = (term4 fn n).
Proof. exact (eq_refl (term16 fn n)). Qed.
Lemma lem123903 (fn : nat -> Prop) (n : nat) : (term15 fn n) = (term4 fn n).
Proof. exact (TRANS (@lem123901 fn n) (@lem123902 fn n)). Qed.
Lemma lem123904 (fn : nat -> Prop) (n : nat) : (term17 fn n) = (term17 fn n).
Proof. exact (eq_refl (term17 fn n)). Qed.
Lemma lem123905 (fn : nat -> Prop) (n : nat) : ((term3 fn n) = (term15 fn n)) = ((term3 fn n) = (term4 fn n)).
Proof. exact (MK_COMB (@lem123904 fn n) (@lem123903 fn n)). Qed.
Lemma lem123906 (fn : nat -> Prop) : (term18 fn) = (term19 fn).
Proof. exact (fun_ext (fun n : nat => @lem123905 fn n)). Qed.
Lemma lem123907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem123908 (fn : nat -> Prop) : (term20 fn) = (term1 fn).
Proof. exact (MK_COMB (@lem123907) (@lem123906 fn)). Qed.
Lemma lem123909 (fn : nat -> Prop) : (term21 fn) = (term21 fn).
Proof. exact (eq_refl (term21 fn)). Qed.
Lemma lem123910 (fn : nat -> Prop) : (term22 fn) = (term5 fn).
Proof. exact (MK_COMB (@lem123909 fn) (@lem123908 fn)). Qed.
Lemma lem123911 : term23 = term24.
Proof. exact (fun_ext (fun fn : nat -> Prop => @lem123910 fn)). Qed.
Lemma lem123912 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem123913 : term11 = term25.
Proof. exact (MK_COMB (@lem123912) (@lem123911)). Qed.
Lemma lem123914 : term25.
Proof. exact (EQ_MP (@lem123913) (@lem123898)). Qed.
Lemma lem123915 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term5 EVEN'.
Proof. exact (h1). Qed.
Lemma lem123916 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term1 EVEN'.
Proof. exact (proj2 (@lem123915 EVEN' h1)). Qed.
Lemma lem123917 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : (term0 EVEN') = True.
Proof. exact (proj1 (@lem123915 EVEN' h1)). Qed.
Lemma lem123918 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term5 EVEN'.
Proof. exact (conj (@lem123917 EVEN' h1) (@lem123916 EVEN' h1)). Qed.
Lemma lem123919 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term25.
Proof. exact (ex_intro term24 EVEN' (@lem123918 EVEN' h1)). Qed.
Lemma lem123920 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem123921 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem123920 h1) (fun EVEN' : nat -> Prop => fun h0 : term24 EVEN' => @lem123919 EVEN' h0)). Qed.
Lemma lem123922 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem123921 h1) (fun h1 : term25 => @lem123914)). Qed.
Lemma lem123923 : term25.
Proof. exact (EQ_MP (@lem123922) (@lem123914)). Qed.
Lemma lem123924 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term25.
Proof. exact (ex_intro term24 EVEN' (@lem123890 EVEN' h1)). Qed.
Lemma lem123925 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem123926 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem123925 h1) (fun EVEN' : nat -> Prop => fun h0 : term24 EVEN' => @lem123924 EVEN' h0)). Qed.
Lemma lem123927 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem123926 h1) (fun h1 : term25 => @lem123923)). Qed.
Lemma lem123928 : term25.
Proof. exact (EQ_MP (@lem123927) (@lem123923)). Qed.
Lemma lem123931 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term5 EVEN'.
Proof. exact (h1). Qed.
Lemma lem123932 (EVEN' : nat -> Prop) (h1 : term5 EVEN') : term25.
Proof. exact (ex_intro term24 EVEN' (@lem123931 EVEN' h1)). Qed.
Lemma lem123933 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem123934 (h1 : term25) : term25.
Proof. exact (ex_elim (@lem123933 h1) (fun EVEN' : nat -> Prop => fun h0 : term24 EVEN' => @lem123932 EVEN' h0)). Qed.
Lemma lem123935 : term25 = term25.
Proof. exact (prop_ext (fun h1 : term25 => @lem123934 h1) (fun h1 : term25 => @lem123928)). Qed.
Lemma lem123936 : term25.
Proof. exact (EQ_MP (@lem123935) (@lem123928)). Qed.
Lemma lem123937 : term26.
Proof. exact (fun _2603 : type1673 => @lem123936). Qed.
Lemma lem123938 {A B : Type'} (P : type1413 A B) : term27 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem123939 {A B : Type'} (P : type1413 A B) : (term27 A B P) = ((term28 A B P) = (term29 A B P)).
Proof. exact (eq_refl (term27 A B P)). Qed.
Lemma lem123942 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem123939 A B P) (@lem123938 A B P)). Qed.
Lemma lem123943 (P : type1287) : (term30 P) = (term31 P).
Proof. exact (@lem123942 type1673 (nat -> Prop) P). Qed.
Lemma lem123944 : term32 = term33.
Proof. exact (@lem123943 term34). Qed.
Lemma lem123945 (_2603 : type1673) : (term35 _2603) = term24.
Proof. exact (eq_refl (term35 _2603)). Qed.
Lemma lem123946 (EVEN' : nat -> Prop) : EVEN' = EVEN'.
Proof. exact (eq_refl EVEN'). Qed.
Lemma lem123947 (_2603 : type1673) (EVEN' : nat -> Prop) : (term36 _2603 EVEN') = (term37 EVEN').
Proof. exact (MK_COMB (@lem123945 _2603) (@lem123946 EVEN')). Qed.
Lemma lem123948 (EVEN' : nat -> Prop) : (term37 EVEN') = (term5 EVEN').
Proof. exact (eq_refl (term37 EVEN')). Qed.
Lemma lem123949 (_2603 : type1673) (EVEN' : nat -> Prop) : (term36 _2603 EVEN') = (term5 EVEN').
Proof. exact (TRANS (@lem123947 _2603 EVEN') (@lem123948 EVEN')). Qed.
Lemma lem123950 (_2603 : type1673) : (term38 _2603) = term24.
Proof. exact (fun_ext (fun EVEN' : nat -> Prop => @lem123949 _2603 EVEN')). Qed.
Lemma lem123951 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem123952 (_2603 : type1673) : (term39 _2603) = term25.
Proof. exact (MK_COMB (@lem123951) (@lem123950 _2603)). Qed.
Lemma lem123953 : term40 = term41.
Proof. exact (fun_ext (fun _2603 : type1673 => @lem123952 _2603)). Qed.
Lemma lem123954 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem123955 : term32 = term26.
Proof. exact (MK_COMB (@lem123954) (@lem123953)). Qed.
Lemma lem123956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem123957 : term42 = term43.
Proof. exact (MK_COMB (@lem123956) (@lem123955)). Qed.
Lemma lem123958 (_2603 : type1673) : (term35 _2603) = term24.
Proof. exact (eq_refl (term35 _2603)). Qed.
Lemma lem123959 (EVEN' : type1291) (_2603 : type1673) : (EVEN' _2603) = (EVEN' _2603).
Proof. exact (eq_refl (EVEN' _2603)). Qed.
Lemma lem123960 (EVEN' : type1291) (_2603 : type1673) : (term44 EVEN' _2603) = (term45 EVEN' _2603).
Proof. exact (MK_COMB (@lem123958 _2603) (@lem123959 EVEN' _2603)). Qed.
Lemma lem123961 (EVEN' : type1291) (_2603 : type1673) : (term45 EVEN' _2603) = (term46 EVEN' _2603).
Proof. exact (eq_refl (term45 EVEN' _2603)). Qed.
Lemma lem123962 (EVEN' : type1291) (_2603 : type1673) : (term44 EVEN' _2603) = (term46 EVEN' _2603).
Proof. exact (TRANS (@lem123960 EVEN' _2603) (@lem123961 EVEN' _2603)). Qed.
Lemma lem123963 (EVEN' : type1291) : (term47 EVEN') = (term48 EVEN').
Proof. exact (fun_ext (fun _2603 : type1673 => @lem123962 EVEN' _2603)). Qed.
Lemma lem123964 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem123965 (EVEN' : type1291) : (term49 EVEN') = (term50 EVEN').
Proof. exact (MK_COMB (@lem123964) (@lem123963 EVEN')). Qed.
Lemma lem123966 : term51 = term52.
Proof. exact (fun_ext (fun EVEN' : type1291 => @lem123965 EVEN')). Qed.
Lemma lem123967 : (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> Prop)) = (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> Prop))). Qed.
Lemma lem123968 : term33 = term53.
Proof. exact (MK_COMB (@lem123967) (@lem123966)). Qed.
Lemma lem123969 : (term32 = term33) = (term26 = term53).
Proof. exact (MK_COMB (@lem123957) (@lem123968)). Qed.
Lemma lem123970 : term26 = term53.
Proof. exact (EQ_MP (@lem123969) (@lem123944)). Qed.
Lemma lem123971 : term53.
Proof. exact (EQ_MP (@lem123970) (@lem123937)). Qed.
Lemma lem123973 {A : Type'} : (@ex A) = (term54 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem123974 : (@ex ((prod nat (prod nat (prod nat nat))) -> nat -> Prop)) = term55.
Proof. exact (@lem123973 type1291). Qed.
Lemma lem123975 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem123976 : term53 = term56.
Proof. exact (MK_COMB (@lem123974) (@lem123975)). Qed.
Lemma lem123977 : term56 = term57.
Proof. exact (eq_refl term56). Qed.
Lemma lem123978 : term53 = term57.
Proof. exact (TRANS (@lem123976) (@lem123977)). Qed.
Lemma lem123979 : term57.
Proof. exact (EQ_MP (@lem123978) (@lem123971)). Qed.
