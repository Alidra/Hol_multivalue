Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm196344_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIVISION_spec.
Require Import DIV_UNIQ_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem195908 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem195909 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem195908 h1 m). Qed.
Lemma lem195910 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem195911 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem195910 m) (@lem195909 m h1)). Qed.
Lemma lem195912 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem195911 m h1 n). Qed.
Lemma lem195913 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem195914 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem195913 m n) (@lem195912 m n h1)). Qed.
Lemma lem195915 (m : nat) (n : nat) (q : nat) (h1 : term0) : term5 m n q.
Proof. exact (@lem195914 m n h1 q). Qed.
Lemma lem195916 (m : nat) (n : nat) (q : nat) : (term5 m n q) = (term6 m n q).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem195917 (m : nat) (n : nat) (q : nat) (h1 : term0) : term6 m n q.
Proof. exact (EQ_MP (@lem195916 m n q) (@lem195915 m n q h1)). Qed.
Lemma lem195918 (m : nat) (n : nat) (q : nat) (r : nat) (h1 : term0) : term7 m n q r.
Proof. exact (@lem195917 m n q h1 r). Qed.
Lemma lem195919 (r : nat) (m : nat) (n : nat) (q : nat) : (term7 m n q r) = (term8 r m n q).
Proof. exact (eq_refl (term7 m n q r)). Qed.
Lemma lem195920 (r : nat) (m : nat) (n : nat) (q : nat) (h1 : term0) : term8 r m n q.
Proof. exact (EQ_MP (@lem195919 r m n q) (@lem195918 m n q r h1)). Qed.
Lemma lem195921 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem195922 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : (Nat.div m n) = q.
Proof. exact (@lem195920 r m n q h1 (@lem195921 m q r n h2)). Qed.
Lemma lem195923 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term10 m n q.
Proof. exact (fun h0 : term0 => @lem195922 m q r n h0 h1). Qed.
Lemma lem195924 (m : nat) (q : nat) (n : nat) (h1 : term11 m q n) : term11 m q n.
Proof. exact (h1). Qed.
Lemma lem195925 (m : nat) (q : nat) (n : nat) (h1 : term11 m q n) : term10 m n q.
Proof. exact (ex_elim (@lem195924 m q n h1) (fun r : nat => fun h0 : term12 m q n r => @lem195923 m q r n h0)). Qed.
Lemma lem195926 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem195927 (m : nat) (q : nat) (n : nat) (h1 : term0) (h2 : term11 m q n) : (Nat.div m n) = q.
Proof. exact (@lem195925 m q n h2 (@lem195926 h1)). Qed.
Lemma lem195928 (m : nat) (n : nat) (q : nat) (h1 : term0) : term13 m n q.
Proof. exact (fun h0 : term11 m q n => @lem195927 m q n h1 h0). Qed.
Lemma lem195929 (m : nat) (n : nat) (h1 : term0) : term14 m n.
Proof. exact (fun q : nat => @lem195928 m n q h1). Qed.
Lemma lem195930 (m : nat) (h1 : term0) : term15 m.
Proof. exact (fun n : nat => @lem195929 m n h1). Qed.
Lemma lem195931 (h1 : term0) : term16.
Proof. exact (fun m : nat => @lem195930 m h1). Qed.
Lemma lem195932 : term17.
Proof. exact (fun h0 : term0 => @lem195931 h0). Qed.
Lemma lem195933 : term16.
Proof. exact (@lem195932 (@lem169759)). Qed.
Lemma lem195934 (m : nat) : term18 m.
Proof. exact (@lem195933 m). Qed.
Lemma lem195935 (m : nat) : (term18 m) = (term15 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem195936 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem195935 m) (@lem195934 m)). Qed.
Lemma lem195937 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem195936 m n). Qed.
Lemma lem195938 (m : nat) (n : nat) : (term19 m n) = (term14 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem195939 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem195938 m n) (@lem195937 m n)). Qed.
Lemma lem195940 (m : nat) (n : nat) (q : nat) : term20 m n q.
Proof. exact (@lem195939 m n q). Qed.
Lemma lem195941 (m : nat) (n : nat) (q : nat) : (term20 m n q) = (term13 m n q).
Proof. exact (eq_refl (term20 m n q)). Qed.
Lemma lem195943 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem195944 (m : nat) (h1 : term21) : term22 m.
Proof. exact (@lem195943 h1 m). Qed.
Lemma lem195945 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem195946 (m : nat) (h1 : term21) : term23 m.
Proof. exact (EQ_MP (@lem195945 m) (@lem195944 m h1)). Qed.
Lemma lem195947 (m : nat) (n : nat) (h1 : term21) : term24 m n.
Proof. exact (@lem195946 m h1 n). Qed.
Lemma lem195948 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem195949 (m : nat) (n : nat) (h1 : term21) : term25 m n.
Proof. exact (EQ_MP (@lem195948 m n) (@lem195947 m n h1)). Qed.
Lemma lem195950 (n : nat) (h1 : term26 n) : term26 n.
Proof. exact (h1). Qed.
Lemma lem195951 (m : nat) (n : nat) (h1 : term21) (h2 : term26 n) : term27 m n.
Proof. exact (@lem195949 m n h1 (@lem195950 n h2)). Qed.
Lemma lem195952 (n : nat) (h1 : term21) (h2 : term26 n) : term28 n.
Proof. exact (fun m : nat => @lem195951 m n h1 h2). Qed.
Lemma lem195953 (n : nat) (h1 : term21) : term29 n.
Proof. exact (fun h0 : term26 n => @lem195952 n h1 h0). Qed.
Lemma lem195954 (h1 : term21) : term30.
Proof. exact (fun n : nat => @lem195953 n h1). Qed.
Lemma lem195955 : term31.
Proof. exact (fun h0 : term21 => @lem195954 h0). Qed.
Lemma lem195956 : term30.
Proof. exact (@lem195955 (@lem157261)). Qed.
Lemma lem195957 (n : nat) : term32 n.
Proof. exact (@lem195956 n). Qed.
Lemma lem195958 (n : nat) : (term32 n) = (term29 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem195960 (n : nat) (h1 : term26 n) : term26 n.
Proof. exact (h1). Qed.
Lemma lem195961 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem195962 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem195966 (n : nat) : term29 n.
Proof. exact (EQ_MP (@lem195958 n) (@lem195957 n)). Qed.
Lemma lem195967 (n : nat) (h1 : term26 n) : term28 n.
Proof. exact (@lem195966 n (@lem195960 n h1)). Qed.
Lemma lem195968 (m : nat) (n : nat) (h1 : term26 n) : term33 n m.
Proof. exact (@lem195967 n h1 m). Qed.
Lemma lem195969 (m : nat) (n : nat) : (term33 n m) = (term27 m n).
Proof. exact (eq_refl (term33 n m)). Qed.
Lemma lem195970 (m : nat) (n : nat) (h1 : term26 n) : term27 m n.
Proof. exact (EQ_MP (@lem195969 m n) (@lem195968 m n h1)). Qed.
Lemma lem195971 (m : nat) (n : nat) (h1 : term26 n) : m = (term34 m n).
Proof. exact (proj1 (@lem195970 m n h1)). Qed.
Lemma lem195972 (n : nat) : (term35 n) = (term35 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem195973 (m : nat) (n : nat) (h1 : term26 n) : (term36 n m) = (term37 m n).
Proof. exact (MK_COMB (@lem195972 n) (@lem195971 m n h1)). Qed.
Lemma lem195974 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem195975 (n : nat) (m : nat) : (term39 n m) = (term39 n m).
Proof. exact (eq_refl (term39 n m)). Qed.
Lemma lem195976 (m : nat) (n : nat) : ((term36 n m) = (term37 m n)) = ((term36 n m) = (term38 m n)).
Proof. exact (MK_COMB (@lem195975 n m) (@lem195974 m n)). Qed.
Lemma lem195977 (m : nat) (n : nat) : (term36 n m) = (Peano.lt m n).
Proof. exact (eq_refl (term36 n m)). Qed.
Lemma lem195978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem195979 (m : nat) (n : nat) : (term39 n m) = (term40 m n).
Proof. exact (MK_COMB (@lem195978) (@lem195977 m n)). Qed.
Lemma lem195980 (m : nat) (n : nat) : (term38 m n) = (term38 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem195981 (m : nat) (n : nat) : ((term36 n m) = (term38 m n)) = ((Peano.lt m n) = (term38 m n)).
Proof. exact (MK_COMB (@lem195979 m n) (@lem195980 m n)). Qed.
Lemma lem195982 (m : nat) (n : nat) : ((term36 n m) = (term37 m n)) = ((Peano.lt m n) = (term38 m n)).
Proof. exact (TRANS (@lem195976 m n) (@lem195981 m n)). Qed.
Lemma lem195983 (m : nat) (n : nat) (h1 : term26 n) : (Peano.lt m n) = (term38 m n).
Proof. exact (EQ_MP (@lem195982 m n) (@lem195973 m n h1)). Qed.
Lemma lem195984 (m : nat) (n : nat) (h1 : term26 n) : (term38 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem195983 m n h1)). Qed.
Lemma lem195985 (m : nat) : term22 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem195986 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem195987 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem195986 m) (@lem195985 m)). Qed.
Lemma lem195988 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem195987 m n). Qed.
Lemma lem195989 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem195990 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem195989 m n) (@lem195988 m n)). Qed.
Lemma lem195991 (n : nat) (h1 : term26 n) : term26 n.
Proof. exact (h1). Qed.
Lemma lem195992 (m : nat) (n : nat) (h1 : term26 n) : term27 m n.
Proof. exact (@lem195990 m n (@lem195991 n h1)). Qed.
Lemma lem195993 (m : nat) (n : nat) (h1 : term26 n) : term41 m n.
Proof. exact (proj2 (@lem195992 m n h1)). Qed.
Lemma lem195994 (m : nat) (n : nat) : (term41 m n) = ((term41 m n) = True).
Proof. exact (@lem7 (term41 m n)). Qed.
Lemma lem195995 (m : nat) (n : nat) (h1 : term26 n) : (term41 m n) = True.
Proof. exact (EQ_MP (@lem195994 m n) (@lem195993 m n h1)). Qed.
Lemma lem196032 : term42.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem196033 (n : nat) : term43 n.
Proof. exact (@lem196032 n). Qed.
Lemma lem196034 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem196066 : term45.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem196067 (n : nat) : term46 n.
Proof. exact (@lem196066 n). Qed.
Lemma lem196068 (n : nat) : (term46 n) = ((term47 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem196070 (n : nat) : term48 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem196102 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem196109 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem196110 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term49 m n) = term50.
Proof. exact (MK_COMB (@lem196109) (@lem196102 m n h1)). Qed.
Lemma lem196123 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem196124 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term51 m n) = (term47 n).
Proof. exact (MK_COMB (@lem196110 m n h1) (@lem196123 n)). Qed.
Lemma lem196126 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem196068 n) (@lem196067 n)). Qed.
Lemma lem196133 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term51 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem196124 m n h1) (@lem196126 n)). Qed.
Lemma lem196134 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem196135 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term52 m n) = term53.
Proof. exact (MK_COMB (@lem196134) (@lem196133 m n h1)). Qed.
Lemma lem196156 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem196157 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term34 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem196135 m n h1) (@lem196156 m n)). Qed.
Lemma lem196159 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem196034 n) (@lem196033 n)). Qed.
Lemma lem196160 (m : nat) (n : nat) : (term54 m n) = (Nat.modulo m n).
Proof. exact (@lem196159 (Nat.modulo m n)). Qed.
Lemma lem196171 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term34 m n) = (Nat.modulo m n).
Proof. exact (TRANS (@lem196157 m n h1) (@lem196160 m n)). Qed.
Lemma lem196172 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem196173 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem196172) (@lem196171 m n h1)). Qed.
Lemma lem196190 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem196191 (m : nat) (n : nat) (h1 : (Nat.div m n) = (NUMERAL 0)) : (term38 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem196173 m n h1) (@lem196190 n)). Qed.
Lemma lem196193 (m : nat) (n : nat) : term57 m n.
Proof. exact (fun h0 : term26 n => @lem195995 m n h0). Qed.
Lemma lem196199 (n : nat) (h1 : term26 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem196070 n (@lem195960 n h1)). Qed.
Lemma lem196202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem196203 (n : nat) (h1 : term26 n) : (term26 n) = (~ False).
Proof. exact (MK_COMB (@lem196202) (@lem196199 n h1)). Qed.
Lemma lem196205 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem196208 (n : nat) (h1 : term26 n) : (term26 n) = True.
Proof. exact (TRANS (@lem196203 n h1) (@lem196205)). Qed.
Lemma lem196209 (n : nat) (h1 : term26 n) : True = (term26 n).
Proof. exact (SYM (@lem196208 n h1)). Qed.
Lemma lem196210 (n : nat) (h1 : term26 n) : term26 n.
Proof. exact (EQ_MP (@lem196209 n h1) (@lem0)). Qed.
Lemma lem196211 (m : nat) (n : nat) (h1 : term26 n) : (term41 m n) = True.
Proof. exact (@lem196193 m n (@lem196210 n h1)). Qed.
Lemma lem196214 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : (term38 m n) = True.
Proof. exact (TRANS (@lem196191 m n h2) (@lem196211 m n h1)). Qed.
Lemma lem196215 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : True = (term38 m n).
Proof. exact (SYM (@lem196214 m n h1 h2)). Qed.
Lemma lem196216 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : term38 m n.
Proof. exact (EQ_MP (@lem196215 m n h1 h2) (@lem0)). Qed.
Lemma lem196217 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : Peano.lt m n.
Proof. exact (EQ_MP (@lem195984 m n h1) (@lem196216 m n h1 h2)). Qed.
Lemma lem196219 (m : nat) (n : nat) (q : nat) : term13 m n q.
Proof. exact (EQ_MP (@lem195941 m n q) (@lem195940 m n q)). Qed.
Lemma lem196220 (m : nat) (n : nat) : term58 m n.
Proof. exact (@lem196219 m n (NUMERAL 0)). Qed.
Lemma lem196241 : term42.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem196242 (n : nat) : term43 n.
Proof. exact (@lem196241 n). Qed.
Lemma lem196243 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem196275 : term45.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem196276 (n : nat) : term46 n.
Proof. exact (@lem196275 n). Qed.
Lemma lem196277 (n : nat) : (term46 n) = ((term47 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem196292 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem196299 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem196277 n) (@lem196276 n)). Qed.
Lemma lem196300 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem196301 (n : nat) : (term59 n) = term53.
Proof. exact (MK_COMB (@lem196300) (@lem196299 n)). Qed.
Lemma lem196302 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem196303 (n : nat) (m : nat) : (term60 n m) = (term44 m).
Proof. exact (MK_COMB (@lem196301 n) (@lem196302 m)). Qed.
Lemma lem196305 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem196243 n) (@lem196242 n)). Qed.
Lemma lem196306 (m : nat) : (term44 m) = m.
Proof. exact (@lem196305 m). Qed.
Lemma lem196307 (n : nat) (m : nat) : (term60 n m) = m.
Proof. exact (TRANS (@lem196303 n m) (@lem196306 m)). Qed.
Lemma lem196308 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem196309 (n : nat) (m : nat) : (m = (term60 n m)) = (m = m).
Proof. exact (MK_COMB (@lem196308 m) (@lem196307 n m)). Qed.
Lemma lem196311 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem196312 (x : nat) : (x = x) = True.
Proof. exact (@lem196311 nat x). Qed.
Lemma lem196313 (m : nat) : (m = m) = True.
Proof. exact (@lem196312 m). Qed.
Lemma lem196314 (n : nat) (m : nat) : (m = (term60 n m)) = True.
Proof. exact (TRANS (@lem196309 n m) (@lem196313 m)). Qed.
Lemma lem196315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem196316 (n : nat) (m : nat) : (term61 n m) = (and True).
Proof. exact (MK_COMB (@lem196315) (@lem196314 n m)). Qed.
Lemma lem196318 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem196292 m n) (@lem195962 m n h1)). Qed.
Lemma lem196319 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term62 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem196316 n m) (@lem196318 m n h1)). Qed.
Lemma lem196321 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem196322 : (True /\ True) = True.
Proof. exact (@lem196321 True). Qed.
Lemma lem196323 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term62 m n) = True.
Proof. exact (TRANS (@lem196319 m n h1) (@lem196322)). Qed.
Lemma lem196324 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (term62 m n).
Proof. exact (SYM (@lem196323 m n h1)). Qed.
Lemma lem196325 (m : nat) (n : nat) (h1 : Peano.lt m n) : term62 m n.
Proof. exact (EQ_MP (@lem196324 m n h1) (@lem0)). Qed.
Lemma lem196326 (m : nat) (n : nat) (h1 : Peano.lt m n) : term63 m n.
Proof. exact (ex_intro (term64 m n) m (@lem196325 m n h1)). Qed.
Lemma lem196327 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (@lem196220 m n (@lem196326 m n h1)). Qed.
Lemma lem196328 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = ((Nat.div m n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : Peano.lt m n => @lem196327 m n h1) (fun h2 : (Nat.div m n) = (NUMERAL 0) => @lem195962 m n h1)). Qed.
Lemma lem196329 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem196328 m n h1) (@lem195962 m n h1)). Qed.
Lemma lem196330 (m : nat) (n : nat) : term65 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem196329 m n h0). Qed.
Lemma lem196331 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n).
Proof. exact (prop_ext (fun h3 : (Nat.div m n) = (NUMERAL 0) => @lem196217 m n h1 h2) (fun h3 : Peano.lt m n => @lem195961 m n h2)). Qed.
Lemma lem196332 (m : nat) (n : nat) (h1 : term26 n) (h2 : (Nat.div m n) = (NUMERAL 0)) : Peano.lt m n.
Proof. exact (EQ_MP (@lem196331 m n h1 h2) (@lem195961 m n h2)). Qed.
Lemma lem196333 (m : nat) (n : nat) (h1 : term26 n) : term66 m n.
Proof. exact (fun h0 : (Nat.div m n) = (NUMERAL 0) => @lem196332 m n h1 h0). Qed.
Lemma lem196334 (m : nat) (n : nat) (h1 : term26 n) : term67 m n.
Proof. exact (conj (@lem196333 m n h1) (@lem196330 m n)). Qed.
Lemma lem196335 (m : nat) (n : nat) : (term67 m n) = (((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n)).
Proof. exact (@lem32 ((Nat.div m n) = (NUMERAL 0)) (Peano.lt m n)). Qed.
Lemma lem196336 (m : nat) (n : nat) (h1 : term26 n) : ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem196335 m n) (@lem196334 m n h1)). Qed.
Lemma lem196337 (m : nat) (n : nat) (h1 : term26 n) : (term26 n) = (((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n)).
Proof. exact (prop_ext (fun h2 : term26 n => @lem196336 m n h1) (fun h2 : ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n) => @lem195960 n h1)). Qed.
Lemma lem196338 (m : nat) (n : nat) (h1 : term26 n) : ((Nat.div m n) = (NUMERAL 0)) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem196337 m n h1) (@lem195960 n h1)). Qed.
Lemma lem196339 (m : nat) (n : nat) : term68 m n.
Proof. exact (fun h0 : term26 n => @lem196338 m n h0). Qed.
Lemma lem196344 (m : nat) : term69 m.
Proof. exact (fun n : nat => @lem196339 m n). Qed.
