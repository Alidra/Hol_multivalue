Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT2_term_abbrevs.
Require Import DIVISION_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import MOD_UNIQ_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem184982 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem184983 (n : nat) (h1 : n = (NUMERAL 0)) : (NUMERAL 0) = n.
Proof. exact (SYM (@lem184982 n h1)). Qed.
Lemma lem184984 (n : nat) (h1 : (NUMERAL 0) = n) : (NUMERAL 0) = n.
Proof. exact (h1). Qed.
Lemma lem184985 (n : nat) (h1 : (NUMERAL 0) = n) : n = (NUMERAL 0).
Proof. exact (SYM (@lem184984 n h1)). Qed.
Lemma lem184986 (n : nat) : (n = (NUMERAL 0)) = ((NUMERAL 0) = n).
Proof. exact (prop_ext (fun h1 : n = (NUMERAL 0) => @lem184983 n h1) (fun h1 : (NUMERAL 0) = n => @lem184985 n h1)). Qed.
Lemma lem184987 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem184988 (n : nat) : (term0 n) = (term1 n).
Proof. exact (MK_COMB (@lem184987) (@lem184986 n)). Qed.
Lemma lem184989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem184990 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem184989) (@lem184988 n)). Qed.
Lemma lem184992 (m : nat) (n : nat) (h1 : m = (term4 m n)) : m = (term4 m n).
Proof. exact (h1). Qed.
Lemma lem184993 (m : nat) (n : nat) (h1 : m = (term4 m n)) : (term4 m n) = m.
Proof. exact (SYM (@lem184992 m n h1)). Qed.
Lemma lem184994 (n : nat) (m : nat) (h1 : (term4 m n) = m) : (term4 m n) = m.
Proof. exact (h1). Qed.
Lemma lem184995 (n : nat) (m : nat) (h1 : (term4 m n) = m) : m = (term4 m n).
Proof. exact (SYM (@lem184994 n m h1)). Qed.
Lemma lem184996 (n : nat) (m : nat) : (m = (term4 m n)) = ((term4 m n) = m).
Proof. exact (prop_ext (fun h1 : m = (term4 m n) => @lem184993 m n h1) (fun h1 : (term4 m n) = m => @lem184995 n m h1)). Qed.
Lemma lem184997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem184998 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem184997) (@lem184996 n m)). Qed.
Lemma lem185000 (m : nat) (n : nat) : (term7 m n) = (term7 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem185001 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem184998 n m) (@lem185000 m n)). Qed.
Lemma lem185002 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem184990 n) (@lem185001 m n)). Qed.
Lemma lem185003 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem185002 m n)). Qed.
Lemma lem185004 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem185005 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem185004) (@lem185003 m)). Qed.
Lemma lem185006 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem185005 m)). Qed.
Lemma lem185007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem185008 : term18 = term19.
Proof. exact (MK_COMB (@lem185007) (@lem185006)). Qed.
Lemma lem185009 : term19.
Proof. exact (EQ_MP (@lem185008) (@lem157261)). Qed.
Lemma lem185013 (n : nat) (m : nat) (p : nat) (h1 : (term20 m n p) = (term21 n m p)) : (term20 m n p) = (term21 n m p).
Proof. exact (h1). Qed.
Lemma lem185014 (n : nat) (m : nat) (p : nat) (h1 : (term20 m n p) = (term21 n m p)) : (term21 n m p) = (term20 m n p).
Proof. exact (SYM (@lem185013 n m p h1)). Qed.
Lemma lem185015 (m : nat) (n : nat) (p : nat) (h1 : (term21 n m p) = (term20 m n p)) : (term21 n m p) = (term20 m n p).
Proof. exact (h1). Qed.
Lemma lem185016 (m : nat) (n : nat) (p : nat) (h1 : (term21 n m p) = (term20 m n p)) : (term20 m n p) = (term21 n m p).
Proof. exact (SYM (@lem185015 m n p h1)). Qed.
Lemma lem185017 (m : nat) (n : nat) (p : nat) : ((term20 m n p) = (term21 n m p)) = ((term21 n m p) = (term20 m n p)).
Proof. exact (prop_ext (fun h1 : (term20 m n p) = (term21 n m p) => @lem185014 n m p h1) (fun h1 : (term21 n m p) = (term20 m n p) => @lem185016 m n p h1)). Qed.
Lemma lem185018 (m : nat) (n : nat) : (term22 n m) = (term23 m n).
Proof. exact (fun_ext (fun p : nat => @lem185017 m n p)). Qed.
Lemma lem185019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem185020 (m : nat) (n : nat) : (term24 n m) = (term25 m n).
Proof. exact (MK_COMB (@lem185019) (@lem185018 m n)). Qed.
Lemma lem185021 (m : nat) : (term26 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem185020 m n)). Qed.
Lemma lem185022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem185023 (m : nat) : (term28 m) = (term29 m).
Proof. exact (MK_COMB (@lem185022) (@lem185021 m)). Qed.
Lemma lem185024 : term30 = term31.
Proof. exact (fun_ext (fun m : nat => @lem185023 m)). Qed.
Lemma lem185025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem185026 : term32 = term33.
Proof. exact (MK_COMB (@lem185025) (@lem185024)). Qed.
Lemma lem185027 : term33.
Proof. exact (EQ_MP (@lem185026) (@lem82055)). Qed.
Lemma lem185028 (m : nat) : term34 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem185029 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem185030 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem185029 m) (@lem185028 m)). Qed.
Lemma lem185031 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem185030 m n). Qed.
Lemma lem185032 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem185033 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem185032 m n) (@lem185031 m n)). Qed.
Lemma lem185034 (m : nat) (n : nat) (p : nat) : term38 m n p.
Proof. exact (@lem185033 m n p). Qed.
Lemma lem185035 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term39 m n p)).
Proof. exact (eq_refl (term38 m n p)). Qed.
Lemma lem185037 (m : nat) : term40 m.
Proof. exact (@lem185027 m). Qed.
Lemma lem185038 (m : nat) : (term40 m) = (term29 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem185039 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem185038 m) (@lem185037 m)). Qed.
Lemma lem185040 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem185039 m n). Qed.
Lemma lem185041 (m : nat) (n : nat) : (term41 m n) = (term25 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem185042 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem185041 m n) (@lem185040 m n)). Qed.
Lemma lem185043 (m : nat) (n : nat) (p : nat) : term42 m n p.
Proof. exact (@lem185042 m n p). Qed.
Lemma lem185044 (m : nat) (n : nat) (p : nat) : (term42 m n p) = ((term21 n m p) = (term20 m n p)).
Proof. exact (eq_refl (term42 m n p)). Qed.
Lemma lem185046 {A : Type'} (x : A) : term43 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem185047 {A : Type'} (x : A) : (term43 A x) = ((x = x) = True).
Proof. exact (eq_refl (term43 A x)). Qed.
Lemma lem185049 (n : nat) (m : nat) (p : nat) : term44 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem185065 (n : nat) (m : nat) (p : nat) : (term45 m n p) = (term45 n m p).
Proof. exact (proj2 (@lem185049 n m p)). Qed.
Lemma lem185066 (a : nat) (b : nat) (c : nat) : (term45 b a c) = (term45 a b c).
Proof. exact (@lem185065 a b c). Qed.
Lemma lem185076 (a : nat) (b : nat) (c : nat) : (term46 a b c) = (term46 a b c).
Proof. exact (eq_refl (term46 a b c)). Qed.
Lemma lem185077 (a : nat) (b : nat) (c : nat) : ((term45 a b c) = (term45 b a c)) = ((term45 a b c) = (term45 a b c)).
Proof. exact (MK_COMB (@lem185076 a b c) (@lem185066 a b c)). Qed.
Lemma lem185079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem185047 A x) (@lem185046 A x)). Qed.
Lemma lem185080 (x : nat) : (x = x) = True.
Proof. exact (@lem185079 nat x). Qed.
Lemma lem185081 (a : nat) (b : nat) (c : nat) : ((term45 a b c) = (term45 a b c)) = True.
Proof. exact (@lem185080 (term45 a b c)). Qed.
Lemma lem185082 (b : nat) (a : nat) (c : nat) : ((term45 a b c) = (term45 b a c)) = True.
Proof. exact (TRANS (@lem185077 a b c) (@lem185081 a b c)). Qed.
Lemma lem185083 (b : nat) (a : nat) (c : nat) : True = ((term45 a b c) = (term45 b a c)).
Proof. exact (SYM (@lem185082 b a c)). Qed.
Lemma lem185085 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem185086 (m : nat) (h1 : term47) : term48 m.
Proof. exact (@lem185085 h1 m). Qed.
Lemma lem185087 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem185088 (m : nat) (h1 : term47) : term49 m.
Proof. exact (EQ_MP (@lem185087 m) (@lem185086 m h1)). Qed.
Lemma lem185089 (m : nat) (n : nat) (h1 : term47) : term50 m n.
Proof. exact (@lem185088 m h1 n). Qed.
Lemma lem185090 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem185091 (m : nat) (n : nat) (h1 : term47) : term51 m n.
Proof. exact (EQ_MP (@lem185090 m n) (@lem185089 m n h1)). Qed.
Lemma lem185092 (m : nat) (n : nat) (q : nat) (h1 : term47) : term52 m n q.
Proof. exact (@lem185091 m n h1 q). Qed.
Lemma lem185093 (q : nat) (m : nat) (n : nat) : (term52 m n q) = (term53 q m n).
Proof. exact (eq_refl (term52 m n q)). Qed.
Lemma lem185094 (q : nat) (m : nat) (n : nat) (h1 : term47) : term53 q m n.
Proof. exact (EQ_MP (@lem185093 q m n) (@lem185092 m n q h1)). Qed.
Lemma lem185095 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term47) : term54 q m n r.
Proof. exact (@lem185094 q m n h1 r). Qed.
Lemma lem185096 (q : nat) (m : nat) (n : nat) (r : nat) : (term54 q m n r) = (term55 q m n r).
Proof. exact (eq_refl (term54 q m n r)). Qed.
Lemma lem185097 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term47) : term55 q m n r.
Proof. exact (EQ_MP (@lem185096 q m n r) (@lem185095 q m n r h1)). Qed.
Lemma lem185098 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term56 m q r n) : term56 m q r n.
Proof. exact (h1). Qed.
Lemma lem185099 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term47) (h2 : term56 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem185097 q m n r h1 (@lem185098 m q r n h2)). Qed.
Lemma lem185100 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term56 m q r n) : term57 m n r.
Proof. exact (fun h0 : term47 => @lem185099 m q r n h0 h1). Qed.
Lemma lem185101 (m : nat) (r : nat) (n : nat) (h1 : term58 m r n) : term58 m r n.
Proof. exact (h1). Qed.
Lemma lem185102 (m : nat) (r : nat) (n : nat) (h1 : term58 m r n) : term57 m n r.
Proof. exact (ex_elim (@lem185101 m r n h1) (fun q : nat => fun h0 : term59 m r n q => @lem185100 m q r n h0)). Qed.
Lemma lem185103 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem185104 (m : nat) (r : nat) (n : nat) (h1 : term47) (h2 : term58 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem185102 m r n h2 (@lem185103 h1)). Qed.
Lemma lem185105 (m : nat) (n : nat) (r : nat) (h1 : term47) : term60 m n r.
Proof. exact (fun h0 : term58 m r n => @lem185104 m r n h1 h0). Qed.
Lemma lem185106 (m : nat) (n : nat) (h1 : term47) : term61 m n.
Proof. exact (fun r : nat => @lem185105 m n r h1). Qed.
Lemma lem185107 (m : nat) (h1 : term47) : term62 m.
Proof. exact (fun n : nat => @lem185106 m n h1). Qed.
Lemma lem185108 (h1 : term47) : term63.
Proof. exact (fun m : nat => @lem185107 m h1). Qed.
Lemma lem185109 : term64.
Proof. exact (fun h0 : term47 => @lem185108 h0). Qed.
Lemma lem185110 : term63.
Proof. exact (@lem185109 (@lem169705)). Qed.
Lemma lem185111 (m : nat) : term65 m.
Proof. exact (@lem185110 m). Qed.
Lemma lem185112 (m : nat) : (term65 m) = (term62 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem185113 (m : nat) : term62 m.
Proof. exact (EQ_MP (@lem185112 m) (@lem185111 m)). Qed.
Lemma lem185114 (m : nat) (n : nat) : term66 m n.
Proof. exact (@lem185113 m n). Qed.
Lemma lem185115 (m : nat) (n : nat) : (term66 m n) = (term61 m n).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem185116 (m : nat) (n : nat) : term61 m n.
Proof. exact (EQ_MP (@lem185115 m n) (@lem185114 m n)). Qed.
Lemma lem185117 (m : nat) (n : nat) (r : nat) : term67 m n r.
Proof. exact (@lem185116 m n r). Qed.
Lemma lem185118 (m : nat) (n : nat) (r : nat) : (term67 m n r) = (term60 m n r).
Proof. exact (eq_refl (term67 m n r)). Qed.
Lemma lem185120 (m : nat) : term68 m.
Proof. exact (@lem9784 (m = (NUMERAL 0))). Qed.
Lemma lem185121 (m : nat) : (term68 m) = (term69 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem185122 (m : nat) : term69 m.
Proof. exact (EQ_MP (@lem185121 m) (@lem185120 m)). Qed.
Lemma lem185124 (m : nat) (h1 : term0 m) : term0 m.
Proof. exact (h1). Qed.
Lemma lem185125 (p : nat) : term68 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem185126 (p : nat) : (term68 p) = (term69 p).
Proof. exact (eq_refl (term68 p)). Qed.
Lemma lem185127 (p : nat) : term69 p.
Proof. exact (EQ_MP (@lem185126 p) (@lem185125 p)). Qed.
Lemma lem185129 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem185130 : term70.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem185156 : term71.
Proof. exact (proj1 (@lem185130)). Qed.
Lemma lem185157 (m : nat) : term72 m.
Proof. exact (@lem185156 m). Qed.
Lemma lem185158 (m : nat) : (term72 m) = ((term73 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term72 m)). Qed.
Lemma lem185164 (n : nat) : term74 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem185165 (n : nat) : (term74 n) = ((term75 n) = n).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem185170 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185171 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem185172 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul m p) = (term73 m).
Proof. exact (MK_COMB (@lem185171 m) (@lem185170 p h1)). Qed.
Lemma lem185174 (m : nat) : (term73 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem185158 m) (@lem185157 m)). Qed.
Lemma lem185175 (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem185172 m p h1) (@lem185174 m)). Qed.
Lemma lem185176 (m : nat) (n : nat) : (term76 m n) = (term76 m n).
Proof. exact (eq_refl (term76 m n)). Qed.
Lemma lem185177 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (term78 m n).
Proof. exact (MK_COMB (@lem185176 m n) (@lem185175 m p h1)). Qed.
Lemma lem185179 (n : nat) : (term75 n) = n.
Proof. exact (EQ_MP (@lem185165 n) (@lem185164 n)). Qed.
Lemma lem185180 (m : nat) (n : nat) : (term78 m n) = (Nat.mul m n).
Proof. exact (@lem185179 (Nat.mul m n)). Qed.
Lemma lem185181 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (Nat.mul m n).
Proof. exact (TRANS (@lem185177 m n p h1) (@lem185180 m n)). Qed.
Lemma lem185182 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem185183 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term79 n m p) = (term80 m n).
Proof. exact (MK_COMB (@lem185182) (@lem185181 m n p h1)). Qed.
Lemma lem185185 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185186 (n : nat) : (Nat.modulo n) = (Nat.modulo n).
Proof. exact (eq_refl (Nat.modulo n)). Qed.
Lemma lem185187 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.modulo n p) = (term75 n).
Proof. exact (MK_COMB (@lem185186 n) (@lem185185 p h1)). Qed.
Lemma lem185189 (n : nat) : (term75 n) = n.
Proof. exact (EQ_MP (@lem185165 n) (@lem185164 n)). Qed.
Lemma lem185190 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.modulo n p) = n.
Proof. exact (TRANS (@lem185187 n p h1) (@lem185189 n)). Qed.
Lemma lem185191 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem185192 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term81 m n p) = (Nat.mul m n).
Proof. exact (MK_COMB (@lem185191 m) (@lem185190 n p h1)). Qed.
Lemma lem185193 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term77 n m p) = (term81 m n p)) = ((Nat.mul m n) = (Nat.mul m n)).
Proof. exact (MK_COMB (@lem185183 m n p h1) (@lem185192 m n p h1)). Qed.
Lemma lem185195 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem185196 (x : nat) : (x = x) = True.
Proof. exact (@lem185195 nat x). Qed.
Lemma lem185197 (m : nat) (n : nat) : ((Nat.mul m n) = (Nat.mul m n)) = True.
Proof. exact (@lem185196 (Nat.mul m n)). Qed.
Lemma lem185198 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term77 n m p) = (term81 m n p)) = True.
Proof. exact (TRANS (@lem185193 m n p h1) (@lem185197 m n)). Qed.
Lemma lem185199 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : True = ((term77 n m p) = (term81 m n p)).
Proof. exact (SYM (@lem185198 m n p h1)). Qed.
Lemma lem185200 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term77 n m p) = (term81 m n p).
Proof. exact (EQ_MP (@lem185199 m n p h1) (@lem0)). Qed.
Lemma lem185285 : term82.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem185286 (n : nat) : term83 n.
Proof. exact (@lem185285 n). Qed.
Lemma lem185287 (n : nat) : (term83 n) = ((term84 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem185289 (n : nat) : term74 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem185290 (n : nat) : (term74 n) = ((term75 n) = n).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem185308 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185309 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem185310 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m) = term85.
Proof. exact (MK_COMB (@lem185309) (@lem185308 m h1)). Qed.
Lemma lem185311 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem185312 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (term84 n).
Proof. exact (MK_COMB (@lem185310 m h1) (@lem185311 n)). Qed.
Lemma lem185314 (n : nat) : (term84 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem185287 n) (@lem185286 n)). Qed.
Lemma lem185315 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem185312 n m h1) (@lem185314 n)). Qed.
Lemma lem185316 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem185317 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term76 m n) = term86.
Proof. exact (MK_COMB (@lem185316) (@lem185315 n m h1)). Qed.
Lemma lem185319 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185320 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem185321 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m) = term85.
Proof. exact (MK_COMB (@lem185320) (@lem185319 m h1)). Qed.
Lemma lem185322 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem185323 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m p) = (term84 p).
Proof. exact (MK_COMB (@lem185321 m h1) (@lem185322 p)). Qed.
Lemma lem185325 (n : nat) : (term84 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem185287 n) (@lem185286 n)). Qed.
Lemma lem185326 (p : nat) : (term84 p) = (NUMERAL 0).
Proof. exact (@lem185325 p). Qed.
Lemma lem185327 (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem185323 p m h1) (@lem185326 p)). Qed.
Lemma lem185328 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term77 n m p) = term87.
Proof. exact (MK_COMB (@lem185317 n m h1) (@lem185327 p m h1)). Qed.
Lemma lem185330 (n : nat) : (term75 n) = n.
Proof. exact (EQ_MP (@lem185290 n) (@lem185289 n)). Qed.
Lemma lem185331 : term87 = (NUMERAL 0).
Proof. exact (@lem185330 (NUMERAL 0)). Qed.
Lemma lem185332 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term77 n m p) = (NUMERAL 0).
Proof. exact (TRANS (@lem185328 n p m h1) (@lem185331)). Qed.
Lemma lem185333 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem185334 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term79 n m p) = term88.
Proof. exact (MK_COMB (@lem185333) (@lem185332 n p m h1)). Qed.
Lemma lem185336 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185337 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem185338 (m : nat) (h1 : m = (NUMERAL 0)) : (Nat.mul m) = term85.
Proof. exact (MK_COMB (@lem185337) (@lem185336 m h1)). Qed.
Lemma lem185339 (n : nat) (p : nat) : (Nat.modulo n p) = (Nat.modulo n p).
Proof. exact (eq_refl (Nat.modulo n p)). Qed.
Lemma lem185340 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term81 m n p) = (term89 n p).
Proof. exact (MK_COMB (@lem185338 m h1) (@lem185339 n p)). Qed.
Lemma lem185342 (n : nat) : (term84 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem185287 n) (@lem185286 n)). Qed.
Lemma lem185343 (n : nat) (p : nat) : (term89 n p) = (NUMERAL 0).
Proof. exact (@lem185342 (Nat.modulo n p)). Qed.
Lemma lem185344 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term81 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem185340 n p m h1) (@lem185343 n p)). Qed.
Lemma lem185345 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term77 n m p) = (term81 m n p)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem185334 n p m h1) (@lem185344 n p m h1)). Qed.
Lemma lem185347 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem185348 (x : nat) : (x = x) = True.
Proof. exact (@lem185347 nat x). Qed.
Lemma lem185349 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem185348 (NUMERAL 0)). Qed.
Lemma lem185350 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : ((term77 n m p) = (term81 m n p)) = True.
Proof. exact (TRANS (@lem185345 n p m h1) (@lem185349)). Qed.
Lemma lem185351 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : True = ((term77 n m p) = (term81 m n p)).
Proof. exact (SYM (@lem185350 n p m h1)). Qed.
Lemma lem185352 (n : nat) (p : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term77 n m p) = (term81 m n p).
Proof. exact (EQ_MP (@lem185351 n p m h1) (@lem0)). Qed.
Lemma lem185421 (m : nat) (n : nat) (r : nat) : term60 m n r.
Proof. exact (EQ_MP (@lem185118 m n r) (@lem185117 m n r)). Qed.
Lemma lem185422 (m : nat) (n : nat) (p : nat) : term90 m n p.
Proof. exact (@lem185421 (Nat.mul m n) (Nat.mul m p) (term81 m n p)). Qed.
Lemma lem185423 (m : nat) : term91 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem185424 (m : nat) : (term91 m) = (term14 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem185425 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem185424 m) (@lem185423 m)). Qed.
Lemma lem185426 (m : nat) (n : nat) : term92 m n.
Proof. exact (@lem185425 m n). Qed.
Lemma lem185427 (m : nat) (n : nat) : (term92 m n) = (term10 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem185428 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem185427 m n) (@lem185426 m n)). Qed.
Lemma lem185429 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem185430 (m : nat) (n : nat) (h1 : term0 n) : term8 m n.
Proof. exact (@lem185428 m n (@lem185429 n h1)). Qed.
Lemma lem185431 (m : nat) (n : nat) (h1 : term0 n) : term7 m n.
Proof. exact (proj2 (@lem185430 m n h1)). Qed.
Lemma lem185432 (m : nat) (n : nat) : (term7 m n) = ((term7 m n) = True).
Proof. exact (@lem7 (term7 m n)). Qed.
Lemma lem185433 (m : nat) (n : nat) (h1 : term0 n) : (term7 m n) = True.
Proof. exact (EQ_MP (@lem185432 m n) (@lem185431 m n h1)). Qed.
Lemma lem185450 (m : nat) : term93 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem185451 (m : nat) : (term93 m) = (term94 m).
Proof. exact (eq_refl (term93 m)). Qed.
Lemma lem185452 (m : nat) : term94 m.
Proof. exact (EQ_MP (@lem185451 m) (@lem185450 m)). Qed.
Lemma lem185453 (m : nat) (n : nat) : term95 m n.
Proof. exact (@lem185452 m n). Qed.
Lemma lem185454 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (eq_refl (term95 m n)). Qed.
Lemma lem185455 (m : nat) (n : nat) : term96 m n.
Proof. exact (EQ_MP (@lem185454 m n) (@lem185453 m n)). Qed.
Lemma lem185456 (m : nat) (n : nat) (p : nat) : term97 m n p.
Proof. exact (@lem185455 m n p). Qed.
Lemma lem185457 (m : nat) (n : nat) (p : nat) : (term97 m n p) = ((term98 n m p) = (term99 m n p)).
Proof. exact (eq_refl (term97 m n p)). Qed.
Lemma lem185459 (p : nat) : term100 p.
Proof. exact (@lem82 (p = (NUMERAL 0))). Qed.
Lemma lem185472 (m : nat) : term100 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem185562 (m : nat) (n : nat) (p : nat) : (term98 n m p) = (term99 m n p).
Proof. exact (EQ_MP (@lem185457 m n p) (@lem185456 m n p)). Qed.
Lemma lem185563 (m : nat) (n : nat) (p : nat) : (term101 n m p) = (term102 m n p).
Proof. exact (@lem185562 m (Nat.modulo n p) p). Qed.
Lemma lem185577 (m : nat) (h1 : term0 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem185472 m (@lem185124 m h1)). Qed.
Lemma lem185580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem185581 (m : nat) (h1 : term0 m) : (term0 m) = (~ False).
Proof. exact (MK_COMB (@lem185580) (@lem185577 m h1)). Qed.
Lemma lem185583 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem185586 (m : nat) (h1 : term0 m) : (term0 m) = True.
Proof. exact (TRANS (@lem185581 m h1) (@lem185583)). Qed.
Lemma lem185587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem185588 (m : nat) (h1 : term0 m) : (term103 m) = (and True).
Proof. exact (MK_COMB (@lem185587) (@lem185586 m h1)). Qed.
Lemma lem185596 (m : nat) (n : nat) : term104 m n.
Proof. exact (fun h0 : term0 n => @lem185433 m n h0). Qed.
Lemma lem185597 (n : nat) (p : nat) : term104 n p.
Proof. exact (@lem185596 n p). Qed.
Lemma lem185603 (p : nat) (h1 : term0 p) : (p = (NUMERAL 0)) = False.
Proof. exact (@lem185459 p (@lem185129 p h1)). Qed.
Lemma lem185606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem185607 (p : nat) (h1 : term0 p) : (term0 p) = (~ False).
Proof. exact (MK_COMB (@lem185606) (@lem185603 p h1)). Qed.
Lemma lem185609 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem185612 (p : nat) (h1 : term0 p) : (term0 p) = True.
Proof. exact (TRANS (@lem185607 p h1) (@lem185609)). Qed.
Lemma lem185613 (p : nat) (h1 : term0 p) : True = (term0 p).
Proof. exact (SYM (@lem185612 p h1)). Qed.
Lemma lem185614 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (EQ_MP (@lem185613 p h1) (@lem0)). Qed.
Lemma lem185615 (n : nat) (p : nat) (h1 : term0 p) : (term7 n p) = True.
Proof. exact (@lem185597 n p (@lem185614 p h1)). Qed.
Lemma lem185618 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term102 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem185588 m h1) (@lem185615 n p h2)). Qed.
Lemma lem185620 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem185621 : (True /\ True) = True.
Proof. exact (@lem185620 True). Qed.
Lemma lem185624 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term102 m n p) = True.
Proof. exact (TRANS (@lem185618 n m p h1 h2) (@lem185621)). Qed.
Lemma lem185625 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term101 n m p) = True.
Proof. exact (TRANS (@lem185563 m n p) (@lem185624 n m p h1 h2)). Qed.
Lemma lem185626 (m : nat) (n : nat) (p : nat) : (term105 m n p) = (term105 m n p).
Proof. exact (eq_refl (term105 m n p)). Qed.
Lemma lem185627 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term106 n m p) = (term107 m n p).
Proof. exact (MK_COMB (@lem185626 m n p) (@lem185625 n m p h1 h2)). Qed.
Lemma lem185629 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem185630 (m : nat) (n : nat) (p : nat) : (term107 m n p) = ((Nat.mul m n) = (term108 m n p)).
Proof. exact (@lem185629 ((Nat.mul m n) = (term108 m n p))). Qed.
Lemma lem185699 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term106 n m p) = ((Nat.mul m n) = (term108 m n p)).
Proof. exact (TRANS (@lem185627 n m p h1 h2) (@lem185630 m n p)). Qed.
Lemma lem185700 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : ((Nat.mul m n) = (term108 m n p)) = (term106 n m p).
Proof. exact (SYM (@lem185699 n m p h1 h2)). Qed.
Lemma lem185704 (b : nat) (a : nat) (c : nat) : (term45 a b c) = (term45 b a c).
Proof. exact (EQ_MP (@lem185083 b a c) (@lem0)). Qed.
Lemma lem185705 (m : nat) (n : nat) (p : nat) : (term109 n m p) = (term110 m n p).
Proof. exact (@lem185704 m (Nat.div n p) p). Qed.
Lemma lem185706 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem185707 (m : nat) (n : nat) (p : nat) : (term111 n m p) = (term112 m n p).
Proof. exact (MK_COMB (@lem185706) (@lem185705 m n p)). Qed.
Lemma lem185708 (m : nat) (n : nat) (p : nat) : (term81 m n p) = (term81 m n p).
Proof. exact (eq_refl (term81 m n p)). Qed.
Lemma lem185709 (m : nat) (n : nat) (p : nat) : (term108 m n p) = (term113 m n p).
Proof. exact (MK_COMB (@lem185707 m n p) (@lem185708 m n p)). Qed.
Lemma lem185710 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem185711 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term108 m n p)) = ((Nat.mul m n) = (term113 m n p)).
Proof. exact (MK_COMB (@lem185710 m n) (@lem185709 m n p)). Qed.
Lemma lem185712 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term113 m n p)) = ((Nat.mul m n) = (term108 m n p)).
Proof. exact (SYM (@lem185711 m n p)). Qed.
Lemma lem185716 (m : nat) (n : nat) (p : nat) : (term21 n m p) = (term20 m n p).
Proof. exact (EQ_MP (@lem185044 m n p) (@lem185043 m n p)). Qed.
Lemma lem185717 (m : nat) (n : nat) (p : nat) : (term113 m n p) = (term114 m n p).
Proof. exact (@lem185716 m (term115 n p) (Nat.modulo n p)). Qed.
Lemma lem185718 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem185719 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term113 m n p)) = ((Nat.mul m n) = (term114 m n p)).
Proof. exact (MK_COMB (@lem185718 m n) (@lem185717 m n p)). Qed.
Lemma lem185721 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term39 m n p).
Proof. exact (EQ_MP (@lem185035 m n p) (@lem185034 m n p)). Qed.
Lemma lem185722 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term114 m n p)) = (term116 m n p).
Proof. exact (@lem185721 m n (term4 n p)). Qed.
Lemma lem185729 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (term113 m n p)) = (term116 m n p).
Proof. exact (TRANS (@lem185719 m n p) (@lem185722 m n p)). Qed.
Lemma lem185730 (m : nat) (n : nat) (p : nat) : (term116 m n p) = ((Nat.mul m n) = (term113 m n p)).
Proof. exact (SYM (@lem185729 m n p)). Qed.
Lemma lem185731 (m : nat) : term117 m.
Proof. exact (@lem185009 m). Qed.
Lemma lem185732 (m : nat) : (term117 m) = (term15 m).
Proof. exact (eq_refl (term117 m)). Qed.
Lemma lem185733 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem185732 m) (@lem185731 m)). Qed.
Lemma lem185734 (m : nat) (n : nat) : term118 m n.
Proof. exact (@lem185733 m n). Qed.
Lemma lem185735 (m : nat) (n : nat) : (term118 m n) = (term11 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem185736 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem185735 m n) (@lem185734 m n)). Qed.
Lemma lem185737 (n : nat) (h1 : term1 n) : term1 n.
Proof. exact (h1). Qed.
Lemma lem185738 (m : nat) (n : nat) (h1 : term1 n) : term9 m n.
Proof. exact (@lem185736 m n (@lem185737 n h1)). Qed.
Lemma lem185747 (m : nat) (n : nat) (h1 : term1 n) : (term4 m n) = m.
Proof. exact (proj1 (@lem185738 m n h1)). Qed.
Lemma lem185756 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem185757 (p : nat) (h1 : p = (NUMERAL 0)) : (NUMERAL 0) = p.
Proof. exact (SYM (@lem185756 p h1)). Qed.
Lemma lem185758 (p : nat) (h1 : (NUMERAL 0) = p) : (NUMERAL 0) = p.
Proof. exact (h1). Qed.
Lemma lem185759 (p : nat) (h1 : (NUMERAL 0) = p) : p = (NUMERAL 0).
Proof. exact (SYM (@lem185758 p h1)). Qed.
Lemma lem185760 (p : nat) : (p = (NUMERAL 0)) = ((NUMERAL 0) = p).
Proof. exact (prop_ext (fun h1 : p = (NUMERAL 0) => @lem185757 p h1) (fun h1 : (NUMERAL 0) = p => @lem185759 p h1)). Qed.
Lemma lem185761 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem185762 (p : nat) : (term0 p) = (term1 p).
Proof. exact (MK_COMB (@lem185761) (@lem185760 p)). Qed.
Lemma lem185763 (p : nat) (h1 : term0 p) : term1 p.
Proof. exact (EQ_MP (@lem185762 p) (@lem185129 p h1)). Qed.
Lemma lem185764 (p : nat) : term119 p.
Proof. exact (@lem82 ((NUMERAL 0) = p)). Qed.
Lemma lem185766 (m : nat) : term100 m.
Proof. exact (@lem82 (m = (NUMERAL 0))). Qed.
Lemma lem185782 (m : nat) (h1 : term0 m) : (m = (NUMERAL 0)) = False.
Proof. exact (@lem185766 m (@lem185124 m h1)). Qed.
Lemma lem185783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem185784 (m : nat) (h1 : term0 m) : (term120 m) = (or False).
Proof. exact (MK_COMB (@lem185783) (@lem185782 m h1)). Qed.
Lemma lem185788 (n : nat) (m : nat) : term121 n m.
Proof. exact (fun h0 : term1 n => @lem185747 m n h0). Qed.
Lemma lem185789 (p : nat) (n : nat) : term121 p n.
Proof. exact (@lem185788 p n). Qed.
Lemma lem185791 (p : nat) (h1 : term0 p) : ((NUMERAL 0) = p) = False.
Proof. exact (@lem185764 p (@lem185763 p h1)). Qed.
Lemma lem185792 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem185793 (p : nat) (h1 : term0 p) : (term1 p) = (~ False).
Proof. exact (MK_COMB (@lem185792) (@lem185791 p h1)). Qed.
Lemma lem185795 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem185796 (p : nat) (h1 : term0 p) : (term1 p) = True.
Proof. exact (TRANS (@lem185793 p h1) (@lem185795)). Qed.
Lemma lem185797 (p : nat) (h1 : term0 p) : True = (term1 p).
Proof. exact (SYM (@lem185796 p h1)). Qed.
Lemma lem185798 (p : nat) (h1 : term0 p) : term1 p.
Proof. exact (EQ_MP (@lem185797 p h1) (@lem0)). Qed.
Lemma lem185799 (n : nat) (p : nat) (h1 : term0 p) : (term4 n p) = n.
Proof. exact (@lem185789 p n (@lem185798 p h1)). Qed.
Lemma lem185800 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem185801 (n : nat) (p : nat) (h1 : term0 p) : (n = (term4 n p)) = (n = n).
Proof. exact (MK_COMB (@lem185800 n) (@lem185799 n p h1)). Qed.
Lemma lem185803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem185804 (x : nat) : (x = x) = True.
Proof. exact (@lem185803 nat x). Qed.
Lemma lem185805 (n : nat) : (n = n) = True.
Proof. exact (@lem185804 n). Qed.
Lemma lem185806 (n : nat) (p : nat) (h1 : term0 p) : (n = (term4 n p)) = True.
Proof. exact (TRANS (@lem185801 n p h1) (@lem185805 n)). Qed.
Lemma lem185807 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term116 m n p) = (False \/ True).
Proof. exact (MK_COMB (@lem185784 m h1) (@lem185806 n p h2)). Qed.
Lemma lem185809 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem185810 : (False \/ True) = True.
Proof. exact (@lem185809 True). Qed.
Lemma lem185811 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term116 m n p) = True.
Proof. exact (TRANS (@lem185807 n m p h1 h2) (@lem185810)). Qed.
Lemma lem185812 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : True = (term116 m n p).
Proof. exact (SYM (@lem185811 n m p h1 h2)). Qed.
Lemma lem185813 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term116 m n p.
Proof. exact (EQ_MP (@lem185812 n m p h1 h2) (@lem0)). Qed.
Lemma lem185814 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (Nat.mul m n) = (term113 m n p).
Proof. exact (EQ_MP (@lem185730 m n p) (@lem185813 n m p h1 h2)). Qed.
Lemma lem185815 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (Nat.mul m n) = (term108 m n p).
Proof. exact (EQ_MP (@lem185712 m n p) (@lem185814 n m p h1 h2)). Qed.
Lemma lem185816 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term106 n m p.
Proof. exact (EQ_MP (@lem185700 n m p h1 h2) (@lem185815 n m p h1 h2)). Qed.
Lemma lem185817 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : term122 n m p.
Proof. exact (ex_intro (term123 n m p) (Nat.div n p) (@lem185816 n m p h1 h2)). Qed.
Lemma lem185819 (n : nat) (m : nat) (p : nat) (h1 : term0 m) (h2 : term0 p) : (term77 n m p) = (term81 m n p).
Proof. exact (@lem185422 m n p (@lem185817 n m p h1 h2)). Qed.
Lemma lem185821 (m : nat) (n : nat) (p : nat) (h1 : term0 p) : (term77 n m p) = (term81 m n p).
Proof. exact (or_elim (@lem185122 m) (fun h0 : m = (NUMERAL 0) => @lem185352 n p m h0) (fun h0 : term0 m => @lem185819 n m p h0 h1)). Qed.
Lemma lem185822 (m : nat) (n : nat) (p : nat) : (term77 n m p) = (term81 m n p).
Proof. exact (or_elim (@lem185127 p) (fun h0 : p = (NUMERAL 0) => @lem185200 m n p h0) (fun h0 : term0 p => @lem185821 m n p h0)). Qed.
Lemma lem185827 (m : nat) (n : nat) : term124 m n.
Proof. exact (fun p : nat => @lem185822 m n p). Qed.
Lemma lem185832 (m : nat) : term125 m.
Proof. exact (fun n : nat => @lem185827 m n). Qed.
Lemma lem185837 : term126.
Proof. exact (fun m : nat => @lem185832 m). Qed.
