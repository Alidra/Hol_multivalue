Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EQ_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import DIVISION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_UNIQ_spec.
Require Import MULT_CLAUSES_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Lemma lem177915 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem177916 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem177915 m n p h1)). Qed.
Lemma lem177917 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem177918 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem177917 m n p h1)). Qed.
Lemma lem177919 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem177916 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem177918 m n p h1)). Qed.
Lemma lem177920 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem177919 m n p)). Qed.
Lemma lem177921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177922 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem177921) (@lem177920 m n)). Qed.
Lemma lem177923 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem177922 m n)). Qed.
Lemma lem177924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177925 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem177924) (@lem177923 m)). Qed.
Lemma lem177926 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem177925 m)). Qed.
Lemma lem177927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177928 : term12 = term13.
Proof. exact (MK_COMB (@lem177927) (@lem177926)). Qed.
Lemma lem177929 : term13.
Proof. exact (EQ_MP (@lem177928) (@lem77960)). Qed.
Lemma lem177930 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem177931 (m : nat) (h1 : term14) : term15 m.
Proof. exact (@lem177930 h1 m). Qed.
Lemma lem177932 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem177933 (m : nat) (h1 : term14) : term16 m.
Proof. exact (EQ_MP (@lem177932 m) (@lem177931 m h1)). Qed.
Lemma lem177934 (m : nat) (n : nat) (h1 : term14) : term17 m n.
Proof. exact (@lem177933 m h1 n). Qed.
Lemma lem177935 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem177936 (m : nat) (n : nat) (h1 : term14) : term18 m n.
Proof. exact (EQ_MP (@lem177935 m n) (@lem177934 m n h1)). Qed.
Lemma lem177937 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem177938 (m : nat) (n : nat) (h1 : term14) (h2 : term19 n) : term20 m n.
Proof. exact (@lem177936 m n h1 (@lem177937 n h2)). Qed.
Lemma lem177939 (n : nat) (h1 : term14) (h2 : term19 n) : term21 n.
Proof. exact (fun m : nat => @lem177938 m n h1 h2). Qed.
Lemma lem177940 (n : nat) (h1 : term14) : term22 n.
Proof. exact (fun h0 : term19 n => @lem177939 n h1 h0). Qed.
Lemma lem177941 (h1 : term14) : term23.
Proof. exact (fun n : nat => @lem177940 n h1). Qed.
Lemma lem177942 : term24.
Proof. exact (fun h0 : term14 => @lem177941 h0). Qed.
Lemma lem177943 : term23.
Proof. exact (@lem177942 (@lem157261)). Qed.
Lemma lem177944 (n : nat) : term25 n.
Proof. exact (@lem177943 n). Qed.
Lemma lem177945 (n : nat) : (term25 n) = (term22 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem177947 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem177948 (m : nat) (h1 : term26) : term27 m.
Proof. exact (@lem177947 h1 m). Qed.
Lemma lem177949 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem177950 (m : nat) (h1 : term26) : term28 m.
Proof. exact (EQ_MP (@lem177949 m) (@lem177948 m h1)). Qed.
Lemma lem177951 (m : nat) (n : nat) (h1 : term26) : term29 m n.
Proof. exact (@lem177950 m h1 n). Qed.
Lemma lem177952 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem177953 (m : nat) (n : nat) (h1 : term26) : term30 m n.
Proof. exact (EQ_MP (@lem177952 m n) (@lem177951 m n h1)). Qed.
Lemma lem177954 (m : nat) (n : nat) (q : nat) (h1 : term26) : term31 m n q.
Proof. exact (@lem177953 m n h1 q). Qed.
Lemma lem177955 (q : nat) (m : nat) (n : nat) : (term31 m n q) = (term32 q m n).
Proof. exact (eq_refl (term31 m n q)). Qed.
Lemma lem177956 (q : nat) (m : nat) (n : nat) (h1 : term26) : term32 q m n.
Proof. exact (EQ_MP (@lem177955 q m n) (@lem177954 m n q h1)). Qed.
Lemma lem177957 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term26) : term33 q m n r.
Proof. exact (@lem177956 q m n h1 r). Qed.
Lemma lem177958 (q : nat) (m : nat) (n : nat) (r : nat) : (term33 q m n r) = (term34 q m n r).
Proof. exact (eq_refl (term33 q m n r)). Qed.
Lemma lem177959 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term26) : term34 q m n r.
Proof. exact (EQ_MP (@lem177958 q m n r) (@lem177957 q m n r h1)). Qed.
Lemma lem177960 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term35 m q r n) : term35 m q r n.
Proof. exact (h1). Qed.
Lemma lem177961 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term26) (h2 : term35 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem177959 q m n r h1 (@lem177960 m q r n h2)). Qed.
Lemma lem177962 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term35 m q r n) : term36 m n r.
Proof. exact (fun h0 : term26 => @lem177961 m q r n h0 h1). Qed.
Lemma lem177963 (m : nat) (r : nat) (n : nat) (h1 : term37 m r n) : term37 m r n.
Proof. exact (h1). Qed.
Lemma lem177964 (m : nat) (r : nat) (n : nat) (h1 : term37 m r n) : term36 m n r.
Proof. exact (ex_elim (@lem177963 m r n h1) (fun q : nat => fun h0 : term38 m r n q => @lem177962 m q r n h0)). Qed.
Lemma lem177965 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem177966 (m : nat) (r : nat) (n : nat) (h1 : term26) (h2 : term37 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem177964 m r n h2 (@lem177965 h1)). Qed.
Lemma lem177967 (m : nat) (n : nat) (r : nat) (h1 : term26) : term39 m n r.
Proof. exact (fun h0 : term37 m r n => @lem177966 m r n h1 h0). Qed.
Lemma lem177968 (m : nat) (n : nat) (h1 : term26) : term40 m n.
Proof. exact (fun r : nat => @lem177967 m n r h1). Qed.
Lemma lem177969 (m : nat) (h1 : term26) : term41 m.
Proof. exact (fun n : nat => @lem177968 m n h1). Qed.
Lemma lem177970 (h1 : term26) : term42.
Proof. exact (fun m : nat => @lem177969 m h1). Qed.
Lemma lem177971 : term43.
Proof. exact (fun h0 : term26 => @lem177970 h0). Qed.
Lemma lem177972 : term42.
Proof. exact (@lem177971 (@lem169705)). Qed.
Lemma lem177973 (m : nat) : term44 m.
Proof. exact (@lem177972 m). Qed.
Lemma lem177974 (m : nat) : (term44 m) = (term41 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem177975 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem177974 m) (@lem177973 m)). Qed.
Lemma lem177976 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem177975 m n). Qed.
Lemma lem177977 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem177978 (m : nat) (n : nat) : term40 m n.
Proof. exact (EQ_MP (@lem177977 m n) (@lem177976 m n)). Qed.
Lemma lem177979 (m : nat) (n : nat) (r : nat) : term46 m n r.
Proof. exact (@lem177978 m n r). Qed.
Lemma lem177980 (m : nat) (n : nat) (r : nat) : (term46 m n r) = (term39 m n r).
Proof. exact (eq_refl (term46 m n r)). Qed.
Lemma lem177982 (p : nat) : term47 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem177983 (p : nat) : (term47 p) = (term48 p).
Proof. exact (eq_refl (term47 p)). Qed.
Lemma lem177984 (p : nat) : term48 p.
Proof. exact (EQ_MP (@lem177983 p) (@lem177982 p)). Qed.
Lemma lem177986 (p : nat) (h1 : term19 p) : term19 p.
Proof. exact (h1). Qed.
Lemma lem177987 : term49.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem178003 : term50.
Proof. exact (proj1 (@lem177987)). Qed.
Lemma lem178004 (m : nat) : term51 m.
Proof. exact (@lem178003 m). Qed.
Lemma lem178005 (m : nat) : (term51 m) = ((term52 m) = m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem178011 : term53.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem178037 : term54.
Proof. exact (proj1 (@lem178011)). Qed.
Lemma lem178038 (m : nat) : term55 m.
Proof. exact (@lem178037 m). Qed.
Lemma lem178039 (m : nat) : (term55 m) = ((term56 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem178052 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178053 (q : nat) : (Nat.mul q) = (Nat.mul q).
Proof. exact (eq_refl (Nat.mul q)). Qed.
Lemma lem178054 (q : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul q p) = (term56 q).
Proof. exact (MK_COMB (@lem178053 q) (@lem178052 p h1)). Qed.
Lemma lem178056 (m : nat) : (term56 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem178039 m) (@lem178038 m)). Qed.
Lemma lem178057 (q : nat) : (term56 q) = (NUMERAL 0).
Proof. exact (@lem178056 q). Qed.
Lemma lem178058 (q : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul q p) = (NUMERAL 0).
Proof. exact (TRANS (@lem178054 q p h1) (@lem178057 q)). Qed.
Lemma lem178059 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem178060 (q : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term57 n q p) = (term52 n).
Proof. exact (MK_COMB (@lem178059 n) (@lem178058 q p h1)). Qed.
Lemma lem178062 (m : nat) : (term52 m) = m.
Proof. exact (EQ_MP (@lem178005 m) (@lem178004 m)). Qed.
Lemma lem178063 (n : nat) : (term52 n) = n.
Proof. exact (@lem178062 n). Qed.
Lemma lem178064 (q : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term57 n q p) = n.
Proof. exact (TRANS (@lem178060 q n p h1) (@lem178063 n)). Qed.
Lemma lem178065 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem178066 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (m = (term57 n q p)) = (m = n).
Proof. exact (MK_COMB (@lem178065 m) (@lem178064 q n p h1)). Qed.
Lemma lem178069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem178070 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term58 m n q p) = (term59 m n).
Proof. exact (MK_COMB (@lem178069) (@lem178066 q m n p h1)). Qed.
Lemma lem178074 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178075 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem178076 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.modulo m p) = (term60 m).
Proof. exact (MK_COMB (@lem178075 m) (@lem178074 p h1)). Qed.
Lemma lem178077 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem178078 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term61 m p) = (term62 m).
Proof. exact (MK_COMB (@lem178077) (@lem178076 m p h1)). Qed.
Lemma lem178080 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178081 (n : nat) : (Nat.modulo n) = (Nat.modulo n).
Proof. exact (eq_refl (Nat.modulo n)). Qed.
Lemma lem178082 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.modulo n p) = (term60 n).
Proof. exact (MK_COMB (@lem178081 n) (@lem178080 p h1)). Qed.
Lemma lem178083 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((Nat.modulo m p) = (Nat.modulo n p)) = ((term60 m) = (term60 n)).
Proof. exact (MK_COMB (@lem178078 m p h1) (@lem178082 n p h1)). Qed.
Lemma lem178086 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term63 q m n p) = (term64 m n).
Proof. exact (MK_COMB (@lem178070 q m n p h1) (@lem178083 m n p h1)). Qed.
Lemma lem178091 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term64 m n) = (term63 q m n p).
Proof. exact (SYM (@lem178086 q m n p h1)). Qed.
Lemma lem178092 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem178093 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem178094 (m : nat) (n : nat) (h1 : m = n) : (term66 n m) = (term67 n).
Proof. exact (MK_COMB (@lem178093 n) (@lem178092 m n h1)). Qed.
Lemma lem178095 (n : nat) : (term67 n) = ((term60 n) = (term60 n)).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem178096 (n : nat) (m : nat) : (term68 n m) = (term68 n m).
Proof. exact (eq_refl (term68 n m)). Qed.
Lemma lem178097 (m : nat) (n : nat) : ((term66 n m) = (term67 n)) = ((term66 n m) = ((term60 n) = (term60 n))).
Proof. exact (MK_COMB (@lem178096 n m) (@lem178095 n)). Qed.
Lemma lem178098 (m : nat) (n : nat) : (term66 n m) = ((term60 m) = (term60 n)).
Proof. exact (eq_refl (term66 n m)). Qed.
Lemma lem178099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem178100 (m : nat) (n : nat) : (term68 n m) = (term69 m n).
Proof. exact (MK_COMB (@lem178099) (@lem178098 m n)). Qed.
Lemma lem178101 (n : nat) : ((term60 n) = (term60 n)) = ((term60 n) = (term60 n)).
Proof. exact (eq_refl ((term60 n) = (term60 n))). Qed.
Lemma lem178102 (m : nat) (n : nat) : ((term66 n m) = ((term60 n) = (term60 n))) = (((term60 m) = (term60 n)) = ((term60 n) = (term60 n))).
Proof. exact (MK_COMB (@lem178100 m n) (@lem178101 n)). Qed.
Lemma lem178103 (m : nat) (n : nat) : ((term66 n m) = (term67 n)) = (((term60 m) = (term60 n)) = ((term60 n) = (term60 n))).
Proof. exact (TRANS (@lem178097 m n) (@lem178102 m n)). Qed.
Lemma lem178104 (m : nat) (n : nat) (h1 : m = n) : ((term60 m) = (term60 n)) = ((term60 n) = (term60 n)).
Proof. exact (EQ_MP (@lem178103 m n) (@lem178094 m n h1)). Qed.
Lemma lem178105 (m : nat) (n : nat) (h1 : m = n) : ((term60 n) = (term60 n)) = ((term60 m) = (term60 n)).
Proof. exact (SYM (@lem178104 m n h1)). Qed.
Lemma lem178106 (n : nat) : (term60 n) = (term60 n).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem178107 (m : nat) (n : nat) (h1 : m = n) : (term60 m) = (term60 n).
Proof. exact (EQ_MP (@lem178105 m n h1) (@lem178106 n)). Qed.
Lemma lem178108 (m : nat) (n : nat) : term64 m n.
Proof. exact (fun h0 : m = n => @lem178107 m n h0). Qed.
Lemma lem178109 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term63 q m n p.
Proof. exact (EQ_MP (@lem178091 q m n p h1) (@lem178108 m n)). Qed.
Lemma lem178110 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term57 n q p)) : m = (term57 n q p).
Proof. exact (h1). Qed.
Lemma lem178111 (n : nat) (p : nat) : (term70 n p) = (term70 n p).
Proof. exact (eq_refl (term70 n p)). Qed.
Lemma lem178112 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term57 n q p)) : (term71 n p m) = (term72 n q p).
Proof. exact (MK_COMB (@lem178111 n p) (@lem178110 m n q p h1)). Qed.
Lemma lem178113 (q : nat) (n : nat) (p : nat) : (term72 n q p) = ((term73 n q p) = (Nat.modulo n p)).
Proof. exact (eq_refl (term72 n q p)). Qed.
Lemma lem178114 (n : nat) (p : nat) (m : nat) : (term74 n p m) = (term74 n p m).
Proof. exact (eq_refl (term74 n p m)). Qed.
Lemma lem178115 (m : nat) (q : nat) (n : nat) (p : nat) : ((term71 n p m) = (term72 n q p)) = ((term71 n p m) = ((term73 n q p) = (Nat.modulo n p))).
Proof. exact (MK_COMB (@lem178114 n p m) (@lem178113 q n p)). Qed.
Lemma lem178116 (m : nat) (n : nat) (p : nat) : (term71 n p m) = ((Nat.modulo m p) = (Nat.modulo n p)).
Proof. exact (eq_refl (term71 n p m)). Qed.
Lemma lem178117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem178118 (m : nat) (n : nat) (p : nat) : (term74 n p m) = (term75 m n p).
Proof. exact (MK_COMB (@lem178117) (@lem178116 m n p)). Qed.
Lemma lem178119 (q : nat) (n : nat) (p : nat) : ((term73 n q p) = (Nat.modulo n p)) = ((term73 n q p) = (Nat.modulo n p)).
Proof. exact (eq_refl ((term73 n q p) = (Nat.modulo n p))). Qed.
Lemma lem178120 (m : nat) (q : nat) (n : nat) (p : nat) : ((term71 n p m) = ((term73 n q p) = (Nat.modulo n p))) = (((Nat.modulo m p) = (Nat.modulo n p)) = ((term73 n q p) = (Nat.modulo n p))).
Proof. exact (MK_COMB (@lem178118 m n p) (@lem178119 q n p)). Qed.
Lemma lem178121 (m : nat) (q : nat) (n : nat) (p : nat) : ((term71 n p m) = (term72 n q p)) = (((Nat.modulo m p) = (Nat.modulo n p)) = ((term73 n q p) = (Nat.modulo n p))).
Proof. exact (TRANS (@lem178115 m q n p) (@lem178120 m q n p)). Qed.
Lemma lem178122 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term57 n q p)) : ((Nat.modulo m p) = (Nat.modulo n p)) = ((term73 n q p) = (Nat.modulo n p)).
Proof. exact (EQ_MP (@lem178121 m q n p) (@lem178112 m n q p h1)). Qed.
Lemma lem178123 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : m = (term57 n q p)) : ((term73 n q p) = (Nat.modulo n p)) = ((Nat.modulo m p) = (Nat.modulo n p)).
Proof. exact (SYM (@lem178122 m n q p h1)). Qed.
Lemma lem178125 (m : nat) (n : nat) (r : nat) : term39 m n r.
Proof. exact (EQ_MP (@lem177980 m n r) (@lem177979 m n r)). Qed.
Lemma lem178126 (q : nat) (n : nat) (p : nat) : term76 q n p.
Proof. exact (@lem178125 (term57 n q p) p (Nat.modulo n p)). Qed.
Lemma lem178128 (n : nat) : term22 n.
Proof. exact (EQ_MP (@lem177945 n) (@lem177944 n)). Qed.
Lemma lem178129 (p : nat) : term22 p.
Proof. exact (@lem178128 p). Qed.
Lemma lem178130 (p : nat) (h1 : term19 p) : term21 p.
Proof. exact (@lem178129 p (@lem177986 p h1)). Qed.
Lemma lem178131 (p : nat) (h1 : term21 p) : term21 p.
Proof. exact (h1). Qed.
Lemma lem178132 (n : nat) (p : nat) (h1 : term21 p) : term77 p n.
Proof. exact (@lem178131 p h1 n). Qed.
Lemma lem178133 (n : nat) (p : nat) : (term77 p n) = (term20 n p).
Proof. exact (eq_refl (term77 p n)). Qed.
Lemma lem178134 (n : nat) (p : nat) (h1 : term21 p) : term20 n p.
Proof. exact (EQ_MP (@lem178133 n p) (@lem178132 n p h1)). Qed.
Lemma lem178136 (n : nat) (p : nat) (h1 : n = (term78 n p)) : n = (term78 n p).
Proof. exact (h1). Qed.
Lemma lem178137 (n : nat) (p : nat) (h1 : n = (term78 n p)) : (term78 n p) = n.
Proof. exact (SYM (@lem178136 n p h1)). Qed.
Lemma lem178138 (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term78 n p) = n.
Proof. exact (h1). Qed.
Lemma lem178139 (p : nat) (n : nat) (h1 : (term78 n p) = n) : n = (term78 n p).
Proof. exact (SYM (@lem178138 p n h1)). Qed.
Lemma lem178140 (p : nat) (n : nat) : (n = (term78 n p)) = ((term78 n p) = n).
Proof. exact (prop_ext (fun h1 : n = (term78 n p) => @lem178137 n p h1) (fun h1 : (term78 n p) = n => @lem178139 p n h1)). Qed.
Lemma lem178141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem178142 (p : nat) (n : nat) : (term79 n p) = (term80 p n).
Proof. exact (MK_COMB (@lem178141) (@lem178140 p n)). Qed.
Lemma lem178144 (n : nat) (p : nat) : (term81 n p) = (term81 n p).
Proof. exact (eq_refl (term81 n p)). Qed.
Lemma lem178145 (n : nat) (p : nat) : (term20 n p) = (term82 n p).
Proof. exact (MK_COMB (@lem178142 p n) (@lem178144 n p)). Qed.
Lemma lem178146 (n : nat) (p : nat) (h1 : term21 p) : term82 n p.
Proof. exact (EQ_MP (@lem178145 n p) (@lem178134 n p h1)). Qed.
Lemma lem178147 (n : nat) (p : nat) (h1 : term81 n p) : term81 n p.
Proof. exact (h1). Qed.
Lemma lem178148 (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term78 n p) = n.
Proof. exact (h1). Qed.
Lemma lem178149 (m : nat) : term83 m.
Proof. exact (@lem177929 m). Qed.
Lemma lem178150 (m : nat) : (term83 m) = (term9 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem178151 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem178150 m) (@lem178149 m)). Qed.
Lemma lem178152 (m : nat) (n : nat) : term84 m n.
Proof. exact (@lem178151 m n). Qed.
Lemma lem178153 (m : nat) (n : nat) : (term84 m n) = (term5 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem178154 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem178153 m n) (@lem178152 m n)). Qed.
Lemma lem178155 (m : nat) (n : nat) (p : nat) : term85 m n p.
Proof. exact (@lem178154 m n p). Qed.
Lemma lem178156 (m : nat) (n : nat) (p : nat) : (term85 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term85 m n p)). Qed.
Lemma lem178158 (m : nat) : term86 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem178159 (m : nat) : (term86 m) = (term87 m).
Proof. exact (eq_refl (term86 m)). Qed.
Lemma lem178160 (m : nat) : term87 m.
Proof. exact (EQ_MP (@lem178159 m) (@lem178158 m)). Qed.
Lemma lem178161 (m : nat) (n : nat) : term88 m n.
Proof. exact (@lem178160 m n). Qed.
Lemma lem178162 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem178163 (m : nat) (n : nat) : term89 m n.
Proof. exact (EQ_MP (@lem178162 m n) (@lem178161 m n)). Qed.
Lemma lem178164 (m : nat) (n : nat) (p : nat) : term90 m n p.
Proof. exact (@lem178163 m n p). Qed.
Lemma lem178165 (m : nat) (n : nat) (p : nat) : (term90 m n p) = ((term91 m n p) = (term92 m n p)).
Proof. exact (eq_refl (term90 m n p)). Qed.
Lemma lem178167 (n : nat) (p : nat) : (term81 n p) = ((term81 n p) = True).
Proof. exact (@lem7 (term81 n p)). Qed.
Lemma lem178174 (m : nat) (n : nat) (p : nat) : (term91 m n p) = (term92 m n p).
Proof. exact (EQ_MP (@lem178165 m n p) (@lem178164 m n p)). Qed.
Lemma lem178175 (q : nat) (n : nat) (p : nat) : (term93 q n p) = (term94 q n p).
Proof. exact (@lem178174 q (Nat.div n p) p). Qed.
Lemma lem178176 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem178177 (q : nat) (n : nat) (p : nat) : (term95 q n p) = (term96 q n p).
Proof. exact (MK_COMB (@lem178176) (@lem178175 q n p)). Qed.
Lemma lem178178 (n : nat) (p : nat) : (Nat.modulo n p) = (Nat.modulo n p).
Proof. exact (eq_refl (Nat.modulo n p)). Qed.
Lemma lem178179 (q : nat) (n : nat) (p : nat) : (term97 q n p) = (term98 q n p).
Proof. exact (MK_COMB (@lem178177 q n p) (@lem178178 n p)). Qed.
Lemma lem178181 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem178156 m n p) (@lem178155 m n p)). Qed.
Lemma lem178182 (q : nat) (n : nat) (p : nat) : (term98 q n p) = (term99 q n p).
Proof. exact (@lem178181 (Nat.mul q p) (term100 n p) (Nat.modulo n p)). Qed.
Lemma lem178184 (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term78 n p) = n.
Proof. exact (h1). Qed.
Lemma lem178185 (q : nat) (p : nat) : (term101 q p) = (term101 q p).
Proof. exact (eq_refl (term101 q p)). Qed.
Lemma lem178186 (q : nat) (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term99 q n p) = (term102 q p n).
Proof. exact (MK_COMB (@lem178185 q p) (@lem178184 p n h1)). Qed.
Lemma lem178187 (q : nat) (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term98 q n p) = (term102 q p n).
Proof. exact (TRANS (@lem178182 q n p) (@lem178186 q p n h1)). Qed.
Lemma lem178188 (q : nat) (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term97 q n p) = (term102 q p n).
Proof. exact (TRANS (@lem178179 q n p) (@lem178187 q p n h1)). Qed.
Lemma lem178189 (n : nat) (q : nat) (p : nat) : (term103 n q p) = (term103 n q p).
Proof. exact (eq_refl (term103 n q p)). Qed.
Lemma lem178190 (q : nat) (p : nat) (n : nat) (h1 : (term78 n p) = n) : ((term57 n q p) = (term97 q n p)) = ((term57 n q p) = (term102 q p n)).
Proof. exact (MK_COMB (@lem178189 n q p) (@lem178188 q p n h1)). Qed.
Lemma lem178193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem178194 (q : nat) (p : nat) (n : nat) (h1 : (term78 n p) = n) : (term104 q n p) = (term105 q p n).
Proof. exact (MK_COMB (@lem178193) (@lem178190 q p n h1)). Qed.
Lemma lem178196 (n : nat) (p : nat) (h1 : term81 n p) : (term81 n p) = True.
Proof. exact (EQ_MP (@lem178167 n p) (@lem178147 n p h1)). Qed.
Lemma lem178197 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : (term106 q n p) = (term107 q p n).
Proof. exact (MK_COMB (@lem178194 q p n h2) (@lem178196 n p h1)). Qed.
Lemma lem178199 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem178200 (q : nat) (p : nat) (n : nat) : (term107 q p n) = ((term57 n q p) = (term102 q p n)).
Proof. exact (@lem178199 ((term57 n q p) = (term102 q p n))). Qed.
Lemma lem178203 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : (term106 q n p) = ((term57 n q p) = (term102 q p n)).
Proof. exact (TRANS (@lem178197 q p n h1 h2) (@lem178200 q p n)). Qed.
Lemma lem178204 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : ((term57 n q p) = (term102 q p n)) = (term106 q n p).
Proof. exact (SYM (@lem178203 q p n h1 h2)). Qed.
Lemma lem178205 (m : nat) : term108 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem178206 (m : nat) : (term108 m) = (term109 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem178207 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem178206 m) (@lem178205 m)). Qed.
Lemma lem178208 (m : nat) (n : nat) : term110 m n.
Proof. exact (@lem178207 m n). Qed.
Lemma lem178209 (n : nat) (m : nat) : (term110 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem178212 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem178209 n m) (@lem178208 m n)). Qed.
Lemma lem178213 (q : nat) (p : nat) (n : nat) : (term57 n q p) = (term102 q p n).
Proof. exact (@lem178212 (Nat.mul q p) n). Qed.
Lemma lem178214 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : term106 q n p.
Proof. exact (EQ_MP (@lem178204 q p n h1 h2) (@lem178213 q p n)). Qed.
Lemma lem178215 (n : nat) (p : nat) (h1 : term21 p) : term81 n p.
Proof. exact (proj2 (@lem178146 n p h1)). Qed.
Lemma lem178216 (n : nat) (p : nat) (h1 : term21 p) : (term78 n p) = n.
Proof. exact (proj1 (@lem178146 n p h1)). Qed.
Lemma lem178217 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : (term81 n p) = (term106 q n p).
Proof. exact (prop_ext (fun h3 : term81 n p => @lem178214 q p n h1 h2) (fun h3 : term106 q n p => @lem178147 n p h1)). Qed.
Lemma lem178218 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : term106 q n p.
Proof. exact (EQ_MP (@lem178217 q p n h1 h2) (@lem178147 n p h1)). Qed.
Lemma lem178219 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : ((term78 n p) = n) = (term106 q n p).
Proof. exact (prop_ext (fun h3 : (term78 n p) = n => @lem178218 q p n h1 h2) (fun h3 : term106 q n p => @lem178148 p n h2)). Qed.
Lemma lem178220 (q : nat) (p : nat) (n : nat) (h1 : term81 n p) (h2 : (term78 n p) = n) : term106 q n p.
Proof. exact (EQ_MP (@lem178219 q p n h1 h2) (@lem178148 p n h2)). Qed.
Lemma lem178221 (q : nat) (p : nat) (n : nat) (h1 : term21 p) (h2 : (term78 n p) = n) : (term81 n p) = (term106 q n p).
Proof. exact (prop_ext (fun h3 : term81 n p => @lem178220 q p n h3 h2) (fun h3 : term106 q n p => @lem178215 n p h1)). Qed.
Lemma lem178222 (q : nat) (p : nat) (n : nat) (h1 : term21 p) (h2 : (term78 n p) = n) : term106 q n p.
Proof. exact (EQ_MP (@lem178221 q p n h1 h2) (@lem178215 n p h1)). Qed.
Lemma lem178223 (q : nat) (n : nat) (p : nat) (h1 : term21 p) : ((term78 n p) = n) = (term106 q n p).
Proof. exact (prop_ext (fun h2 : (term78 n p) = n => @lem178222 q p n h1 h2) (fun h2 : term106 q n p => @lem178216 n p h1)). Qed.
Lemma lem178224 (q : nat) (n : nat) (p : nat) (h1 : term21 p) : term106 q n p.
Proof. exact (EQ_MP (@lem178223 q n p h1) (@lem178216 n p h1)). Qed.
Lemma lem178225 (q : nat) (n : nat) (p : nat) : term111 q n p.
Proof. exact (fun h0 : term21 p => @lem178224 q n p h0). Qed.
Lemma lem178226 (q : nat) (n : nat) (p : nat) (h1 : term19 p) : term106 q n p.
Proof. exact (@lem178225 q n p (@lem178130 p h1)). Qed.
Lemma lem178227 (q : nat) (n : nat) (p : nat) (h1 : term19 p) : term112 q n p.
Proof. exact (ex_intro (term113 q n p) (term114 q n p) (@lem178226 q n p h1)). Qed.
Lemma lem178228 (q : nat) (n : nat) (p : nat) (h1 : term19 p) : (term73 n q p) = (Nat.modulo n p).
Proof. exact (@lem178126 q n p (@lem178227 q n p h1)). Qed.
Lemma lem178229 (m : nat) (n : nat) (q : nat) (p : nat) (h1 : term19 p) (h2 : m = (term57 n q p)) : (Nat.modulo m p) = (Nat.modulo n p).
Proof. exact (EQ_MP (@lem178123 m n q p h2) (@lem178228 q n p h1)). Qed.
Lemma lem178230 (q : nat) (m : nat) (n : nat) (p : nat) (h1 : term19 p) : term63 q m n p.
Proof. exact (fun h0 : m = (term57 n q p) => @lem178229 m n q p h1 h0). Qed.
Lemma lem178231 (q : nat) (m : nat) (n : nat) (p : nat) : term63 q m n p.
Proof. exact (or_elim (@lem177984 p) (fun h0 : p = (NUMERAL 0) => @lem178109 q m n p h0) (fun h0 : term19 p => @lem178230 q m n p h0)). Qed.
Lemma lem178236 (m : nat) (n : nat) (p : nat) : term115 m n p.
Proof. exact (fun q : nat => @lem178231 q m n p). Qed.
Lemma lem178241 (m : nat) (n : nat) : term116 m n.
Proof. exact (fun p : nat => @lem178236 m n p). Qed.
Lemma lem178246 (m : nat) : term117 m.
Proof. exact (fun n : nat => @lem178241 m n). Qed.
Lemma lem178251 : term118.
Proof. exact (fun m : nat => @lem178246 m). Qed.
