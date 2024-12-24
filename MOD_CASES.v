Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_CASES_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import LT_ADD2_spec.
Require Import LT_ADD_RCANCEL_spec.
Require Import MOD_LT_spec.
Require Import MOD_UNIQ_spec.
Require Import MULT_2_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_LT_spec.
Require Import SUB_ADD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem174013 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem174014 : term1.
Proof. exact (proj2 (@lem174013)). Qed.
Lemma lem174035 : term2.
Proof. exact (proj1 (@lem174014)). Qed.
Lemma lem174036 (n : nat) : term3 n.
Proof. exact (@lem174035 n). Qed.
Lemma lem174037 (n : nat) : (term3 n) = ((term4 n) = n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem174047 (m : nat) : term5 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem174048 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem174049 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem174048 m) (@lem174047 m)). Qed.
Lemma lem174050 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem174049 m n). Qed.
Lemma lem174051 (n : nat) (m : nat) : (term7 m n) = ((term8 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem174053 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem174054 (m : nat) (h1 : term9) : term10 m.
Proof. exact (@lem174053 h1 m). Qed.
Lemma lem174055 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem174056 (m : nat) (h1 : term9) : term11 m.
Proof. exact (EQ_MP (@lem174055 m) (@lem174054 m h1)). Qed.
Lemma lem174057 (m : nat) (n : nat) (h1 : term9) : term12 m n.
Proof. exact (@lem174056 m h1 n). Qed.
Lemma lem174058 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem174059 (m : nat) (n : nat) (h1 : term9) : term13 m n.
Proof. exact (EQ_MP (@lem174058 m n) (@lem174057 m n h1)). Qed.
Lemma lem174060 (m : nat) (n : nat) (q : nat) (h1 : term9) : term14 m n q.
Proof. exact (@lem174059 m n h1 q). Qed.
Lemma lem174061 (q : nat) (m : nat) (n : nat) : (term14 m n q) = (term15 q m n).
Proof. exact (eq_refl (term14 m n q)). Qed.
Lemma lem174062 (q : nat) (m : nat) (n : nat) (h1 : term9) : term15 q m n.
Proof. exact (EQ_MP (@lem174061 q m n) (@lem174060 m n q h1)). Qed.
Lemma lem174063 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term9) : term16 q m n r.
Proof. exact (@lem174062 q m n h1 r). Qed.
Lemma lem174064 (q : nat) (m : nat) (n : nat) (r : nat) : (term16 q m n r) = (term17 q m n r).
Proof. exact (eq_refl (term16 q m n r)). Qed.
Lemma lem174065 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term9) : term17 q m n r.
Proof. exact (EQ_MP (@lem174064 q m n r) (@lem174063 q m n r h1)). Qed.
Lemma lem174066 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term18 m q r n) : term18 m q r n.
Proof. exact (h1). Qed.
Lemma lem174067 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9) (h2 : term18 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem174065 q m n r h1 (@lem174066 m q r n h2)). Qed.
Lemma lem174068 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term18 m q r n) : term19 m n r.
Proof. exact (fun h0 : term9 => @lem174067 m q r n h0 h1). Qed.
Lemma lem174069 (m : nat) (r : nat) (n : nat) (h1 : term20 m r n) : term20 m r n.
Proof. exact (h1). Qed.
Lemma lem174070 (m : nat) (r : nat) (n : nat) (h1 : term20 m r n) : term19 m n r.
Proof. exact (ex_elim (@lem174069 m r n h1) (fun q : nat => fun h0 : term21 m r n q => @lem174068 m q r n h0)). Qed.
Lemma lem174071 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem174072 (m : nat) (r : nat) (n : nat) (h1 : term9) (h2 : term20 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem174070 m r n h2 (@lem174071 h1)). Qed.
Lemma lem174073 (m : nat) (n : nat) (r : nat) (h1 : term9) : term22 m n r.
Proof. exact (fun h0 : term20 m r n => @lem174072 m r n h1 h0). Qed.
Lemma lem174074 (m : nat) (n : nat) (h1 : term9) : term23 m n.
Proof. exact (fun r : nat => @lem174073 m n r h1). Qed.
Lemma lem174075 (m : nat) (h1 : term9) : term24 m.
Proof. exact (fun n : nat => @lem174074 m n h1). Qed.
Lemma lem174076 (h1 : term9) : term25.
Proof. exact (fun m : nat => @lem174075 m h1). Qed.
Lemma lem174077 : term26.
Proof. exact (fun h0 : term9 => @lem174076 h0). Qed.
Lemma lem174078 : term25.
Proof. exact (@lem174077 (@lem169705)). Qed.
Lemma lem174079 (m : nat) : term27 m.
Proof. exact (@lem174078 m). Qed.
Lemma lem174080 (m : nat) : (term27 m) = (term24 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem174081 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem174080 m) (@lem174079 m)). Qed.
Lemma lem174082 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem174081 m n). Qed.
Lemma lem174083 (m : nat) (n : nat) : (term28 m n) = (term23 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem174084 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem174083 m n) (@lem174082 m n)). Qed.
Lemma lem174085 (m : nat) (n : nat) (r : nat) : term29 m n r.
Proof. exact (@lem174084 m n r). Qed.
Lemma lem174086 (m : nat) (n : nat) (r : nat) : (term29 m n r) = (term22 m n r).
Proof. exact (eq_refl (term29 m n r)). Qed.
Lemma lem174088 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem174089 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term31 _476 _475 _474 _477) = (term32 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem174090 (_474 : nat) (_475 : Prop) (n : nat) (p : nat) (_477 : nat) : (term33 n p _475 _474 _477) = (term34 _474 _475 n p _477).
Proof. exact (@lem174089 _474 _475 (term35 n p) _477). Qed.
Lemma lem174091 (n : nat) (p : nat) : (term36 n p) = (term37 n p).
Proof. exact (@lem174090 n (Peano.lt n p) n p (Nat.sub n p)). Qed.
Lemma lem174092 (n : nat) (p : nat) : (term38 n p) = ((Nat.modulo n p) = (Nat.sub n p)).
Proof. exact (eq_refl (term38 n p)). Qed.
Lemma lem174093 (n : nat) (p : nat) : (term39 n p) = (term39 n p).
Proof. exact (eq_refl (term39 n p)). Qed.
Lemma lem174094 (n : nat) (p : nat) : (term40 n p) = (term41 n p).
Proof. exact (MK_COMB (@lem174093 n p) (@lem174092 n p)). Qed.
Lemma lem174095 (p : nat) (n : nat) : (term42 p n) = ((Nat.modulo n p) = n).
Proof. exact (eq_refl (term42 p n)). Qed.
Lemma lem174096 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (eq_refl (term43 n p)). Qed.
Lemma lem174097 (p : nat) (n : nat) : (term44 p n) = (term45 p n).
Proof. exact (MK_COMB (@lem174096 n p) (@lem174095 p n)). Qed.
Lemma lem174098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem174099 (p : nat) (n : nat) : (term46 p n) = (term47 p n).
Proof. exact (MK_COMB (@lem174098) (@lem174097 p n)). Qed.
Lemma lem174100 (n : nat) (p : nat) : (term37 n p) = (term48 n p).
Proof. exact (MK_COMB (@lem174099 p n) (@lem174094 n p)). Qed.
Lemma lem174101 (n : nat) (p : nat) : (term36 n p) = ((Nat.modulo n p) = (term49 n p)).
Proof. exact (eq_refl (term36 n p)). Qed.
Lemma lem174102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem174103 (n : nat) (p : nat) : (term50 n p) = (term51 n p).
Proof. exact (MK_COMB (@lem174102) (@lem174101 n p)). Qed.
Lemma lem174104 (n : nat) (p : nat) : ((term36 n p) = (term37 n p)) = (((Nat.modulo n p) = (term49 n p)) = (term48 n p)).
Proof. exact (MK_COMB (@lem174103 n p) (@lem174100 n p)). Qed.
Lemma lem174105 (n : nat) (p : nat) : ((Nat.modulo n p) = (term49 n p)) = (term48 n p).
Proof. exact (EQ_MP (@lem174104 n p) (@lem174091 n p)). Qed.
Lemma lem174106 (n : nat) (p : nat) : (term48 n p) = ((Nat.modulo n p) = (term49 n p)).
Proof. exact (SYM (@lem174105 n p)). Qed.
Lemma lem174107 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem174124 (n : nat) (p : nat) (h1 : term8 n p) : term8 n p.
Proof. exact (h1). Qed.
Lemma lem174141 (m : nat) : term52 m.
Proof. exact (@lem170673 m). Qed.
Lemma lem174142 (m : nat) : (term52 m) = (term53 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem174143 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem174142 m) (@lem174141 m)). Qed.
Lemma lem174144 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem174143 m n). Qed.
Lemma lem174145 (n : nat) (m : nat) : (term54 m n) = (term45 n m).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem174146 (n : nat) (m : nat) : term45 n m.
Proof. exact (EQ_MP (@lem174145 n m) (@lem174144 m n)). Qed.
Lemma lem174147 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem174148 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem174146 n m (@lem174147 m n h1)). Qed.
Lemma lem174156 (n : nat) (p : nat) : (Peano.lt n p) = ((Peano.lt n p) = True).
Proof. exact (@lem7 (Peano.lt n p)). Qed.
Lemma lem174161 (n : nat) (m : nat) : term45 n m.
Proof. exact (fun h0 : Peano.lt m n => @lem174148 m n h0). Qed.
Lemma lem174162 (p : nat) (n : nat) : term45 p n.
Proof. exact (@lem174161 p n). Qed.
Lemma lem174164 (n : nat) (p : nat) (h1 : Peano.lt n p) : (Peano.lt n p) = True.
Proof. exact (EQ_MP (@lem174156 n p) (@lem174107 n p h1)). Qed.
Lemma lem174165 (n : nat) (p : nat) (h1 : Peano.lt n p) : True = (Peano.lt n p).
Proof. exact (SYM (@lem174164 n p h1)). Qed.
Lemma lem174166 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (EQ_MP (@lem174165 n p h1) (@lem0)). Qed.
Lemma lem174167 (n : nat) (p : nat) (h1 : Peano.lt n p) : (Nat.modulo n p) = n.
Proof. exact (@lem174162 p n (@lem174166 n p h1)). Qed.
Lemma lem174168 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem174169 (n : nat) (p : nat) (h1 : Peano.lt n p) : (term55 n p) = (@eq nat n).
Proof. exact (MK_COMB (@lem174168) (@lem174167 n p h1)). Qed.
Lemma lem174170 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem174171 (n : nat) (p : nat) (h1 : Peano.lt n p) : ((Nat.modulo n p) = n) = (n = n).
Proof. exact (MK_COMB (@lem174169 n p h1) (@lem174170 n)). Qed.
Lemma lem174173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem174174 (x : nat) : (x = x) = True.
Proof. exact (@lem174173 nat x). Qed.
Lemma lem174175 (n : nat) : (n = n) = True.
Proof. exact (@lem174174 n). Qed.
Lemma lem174176 (n : nat) (p : nat) (h1 : Peano.lt n p) : ((Nat.modulo n p) = n) = True.
Proof. exact (TRANS (@lem174171 n p h1) (@lem174175 n)). Qed.
Lemma lem174177 (n : nat) (p : nat) (h1 : Peano.lt n p) : True = ((Nat.modulo n p) = n).
Proof. exact (SYM (@lem174176 n p h1)). Qed.
Lemma lem174207 (m : nat) (n : nat) (r : nat) : term22 m n r.
Proof. exact (EQ_MP (@lem174086 m n r) (@lem174085 m n r)). Qed.
Lemma lem174208 (n : nat) (p : nat) : term56 n p.
Proof. exact (@lem174207 n p (Nat.sub n p)). Qed.
Lemma lem174210 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem174212 (n : nat) (m : nat) : (term8 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem174051 n m) (@lem174050 m n)). Qed.
Lemma lem174213 (p : nat) (n : nat) : (term8 n p) = (Peano.le p n).
Proof. exact (@lem174212 p n). Qed.
Lemma lem174214 (n : nat) (p : nat) (h1 : term8 n p) : Peano.le p n.
Proof. exact (EQ_MP (@lem174213 p n) (@lem174124 n p h1)). Qed.
Lemma lem174218 (n : nat) : (term4 n) = n.
Proof. exact (EQ_MP (@lem174037 n) (@lem174036 n)). Qed.
Lemma lem174219 (p : nat) : (term4 p) = p.
Proof. exact (@lem174218 p). Qed.
Lemma lem174220 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem174221 (p : nat) : (term57 p) = (Nat.add p).
Proof. exact (MK_COMB (@lem174220) (@lem174219 p)). Qed.
Lemma lem174222 (n : nat) (p : nat) : (Nat.sub n p) = (Nat.sub n p).
Proof. exact (eq_refl (Nat.sub n p)). Qed.
Lemma lem174223 (n : nat) (p : nat) : (term58 n p) = (term59 n p).
Proof. exact (MK_COMB (@lem174221 p) (@lem174222 n p)). Qed.
Lemma lem174224 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem174225 (n : nat) (p : nat) : (n = (term58 n p)) = (n = (term59 n p)).
Proof. exact (MK_COMB (@lem174224 n) (@lem174223 n p)). Qed.
Lemma lem174228 (n : nat) (p : nat) : (n = (term59 n p)) = (n = (term58 n p)).
Proof. exact (SYM (@lem174225 n p)). Qed.
Lemma lem174230 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem174231 (n : nat) (p : nat) : (n = (term59 n p)) = (term61 n p).
Proof. exact (@lem174230 (n = (term59 n p))). Qed.
Lemma lem174232 (n : nat) (p : nat) : (term61 n p) = (n = (term59 n p)).
Proof. exact (SYM (@lem174231 n p)). Qed.
Lemma lem174233 (n : nat) (p : nat) (h1 : term62 n p) : term62 n p.
Proof. exact (h1). Qed.
Lemma lem174236 (n : nat) (p : nat) (h1 : term63 n p) : term63 n p.
Proof. exact (h1). Qed.
Lemma lem174237 (n : nat) (p : nat) : term64 n p.
Proof. exact (fun h0 : term63 n p => @lem174236 n p h0). Qed.
Lemma lem174238 (n : nat) (p : nat) (h1 : term64 n p) : term64 n p.
Proof. exact (h1). Qed.
Lemma lem174239 (n : nat) (p : nat) (h1 : term63 n p) : term63 n p.
Proof. exact (h1). Qed.
Lemma lem174240 (n : nat) (p : nat) (h1 : term63 n p) (h2 : term64 n p) : term63 n p.
Proof. exact (@lem174238 n p h2 (@lem174239 n p h1)). Qed.
Lemma lem174241 (n : nat) (p : nat) (h1 : term63 n p) : term65 n p.
Proof. exact (fun h0 : term64 n p => @lem174240 n p h1 h0). Qed.
Lemma lem174242 (n : nat) (p : nat) (h1 : term64 n p) : term64 n p.
Proof. exact (h1). Qed.
Lemma lem174243 (n : nat) (p : nat) (h1 : term63 n p) (h2 : term64 n p) : term63 n p.
Proof. exact (@lem174241 n p h1 (@lem174242 n p h2)). Qed.
Lemma lem174244 (n : nat) (p : nat) (h1 : term64 n p) : term64 n p.
Proof. exact (fun h0 : term63 n p => @lem174243 n p h0 h1). Qed.
Lemma lem174245 (n : nat) (p : nat) : term66 n p.
Proof. exact (fun h0 : term64 n p => @lem174244 n p h0). Qed.
Lemma lem174248 (n : nat) (p : nat) : term64 n p.
Proof. exact (@lem174245 n p (@lem174237 n p)). Qed.
Lemma lem174274 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem174275 : term67 = term68.
Proof. exact (@lem174274 term69). Qed.
Lemma lem174286 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem174287 : term71 = term72.
Proof. exact (MK_COMB (@lem174286) (@lem174275)). Qed.
Lemma lem174290 (n : nat) (p : nat) : (term73 n p) = (term73 n p).
Proof. exact (eq_refl (term73 n p)). Qed.
Lemma lem174291 (n : nat) (p : nat) : (term74 n p) = (term75 n p).
Proof. exact (MK_COMB (@lem174290 n p) (@lem174287)). Qed.
Lemma lem174294 (p : nat) (n : nat) : (term76 p n) = (term76 p n).
Proof. exact (eq_refl (term76 p n)). Qed.
Lemma lem174295 (n : nat) (p : nat) : (term77 n p) = (term78 n p).
Proof. exact (MK_COMB (@lem174294 p n) (@lem174291 n p)). Qed.
Lemma lem174298 (n : nat) (p : nat) : (term79 n p) = (term79 n p).
Proof. exact (eq_refl (term79 n p)). Qed.
Lemma lem174299 (n : nat) (p : nat) : (term63 n p) = (term80 n p).
Proof. exact (MK_COMB (@lem174298 n p) (@lem174295 n p)). Qed.
Lemma lem174302 (p : nat) : (term81 p) = (term82 p).
Proof. exact (fun_ext (fun n : nat => @lem174299 n p)). Qed.
Lemma lem174303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174304 (p : nat) : (term83 p) = (term84 p).
Proof. exact (MK_COMB (@lem174303) (@lem174302 p)). Qed.
Lemma lem174309 : term85 = term86.
Proof. exact (fun_ext (fun p : nat => @lem174304 p)). Qed.
Lemma lem174310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174319 : term87 = term88.
Proof. exact (MK_COMB (@lem174310) (@lem174309)). Qed.
Lemma lem174324 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem174325 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem174324 n m)). Qed.
Lemma lem174326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174327 (m : nat) : (term91 m) = (term91 m).
Proof. exact (MK_COMB (@lem174326) (@lem174325 m)). Qed.
Lemma lem174328 : term92 = term92.
Proof. exact (fun_ext (fun m : nat => @lem174327 m)). Qed.
Lemma lem174329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174330 : term69 = term69.
Proof. exact (MK_COMB (@lem174329) (@lem174328)). Qed.
Lemma lem174331 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem174332 : term68 = term68.
Proof. exact (MK_COMB (@lem174331) (@lem174330)). Qed.
Lemma lem174333 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem174334 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem174333 n m)). Qed.
Lemma lem174335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174336 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem174335) (@lem174334 m)). Qed.
Lemma lem174337 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem174336 m)). Qed.
Lemma lem174338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174339 : term96 = term96.
Proof. exact (MK_COMB (@lem174338) (@lem174337)). Qed.
Lemma lem174340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem174341 : term70 = term70.
Proof. exact (MK_COMB (@lem174340) (@lem174339)). Qed.
Lemma lem174342 : term72 = term72.
Proof. exact (MK_COMB (@lem174341) (@lem174332)). Qed.
Lemma lem174347 (n : nat) (p : nat) : (term73 n p) = (term73 n p).
Proof. exact (eq_refl (term73 n p)). Qed.
Lemma lem174348 (n : nat) (p : nat) : (term75 n p) = (term75 n p).
Proof. exact (MK_COMB (@lem174347 n p) (@lem174342)). Qed.
Lemma lem174351 (p : nat) (n : nat) : (term76 p n) = (term76 p n).
Proof. exact (eq_refl (term76 p n)). Qed.
Lemma lem174352 (n : nat) (p : nat) : (term78 n p) = (term78 n p).
Proof. exact (MK_COMB (@lem174351 p n) (@lem174348 n p)). Qed.
Lemma lem174355 (n : nat) (p : nat) : (term79 n p) = (term79 n p).
Proof. exact (eq_refl (term79 n p)). Qed.
Lemma lem174356 (n : nat) (p : nat) : (term80 n p) = (term80 n p).
Proof. exact (MK_COMB (@lem174355 n p) (@lem174352 n p)). Qed.
Lemma lem174357 (p : nat) : (term82 p) = (term82 p).
Proof. exact (fun_ext (fun n : nat => @lem174356 n p)). Qed.
Lemma lem174358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174359 (p : nat) : (term84 p) = (term84 p).
Proof. exact (MK_COMB (@lem174358) (@lem174357 p)). Qed.
Lemma lem174360 : term86 = term86.
Proof. exact (fun_ext (fun p : nat => @lem174359 p)). Qed.
Lemma lem174361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174362 : term88 = term88.
Proof. exact (MK_COMB (@lem174361) (@lem174360)). Qed.
Lemma lem174411 : term87 = term88.
Proof. exact (TRANS (@lem174319) (@lem174362)). Qed.
Lemma lem174412 : term88 = term87.
Proof. exact (SYM (@lem174411)). Qed.
Lemma lem174416 (h1 : term96) : term96.
Proof. exact (h1). Qed.
Lemma lem174417 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem174429 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem174435 (n : nat) (p : nat) (h1 : term62 n p) : term62 n p.
Proof. exact (h1). Qed.
Lemma lem174436 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem174437 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem174436 n m)). Qed.
Lemma lem174438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174439 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem174438) (@lem174437 m)). Qed.
Lemma lem174440 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem174439 m)). Qed.
Lemma lem174441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174454 : term96 = term96.
Proof. exact (MK_COMB (@lem174441) (@lem174440)). Qed.
Lemma lem174455 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem174454) (@lem174416 h1)). Qed.
Lemma lem174462 (n : nat) (m : nat) : (term89 n m) = (term97 n m).
Proof. exact (@lem17265 (Peano.le n m) ((term98 m n) = m)). Qed.
Lemma lem174463 (m : nat) : (term90 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem174462 n m)). Qed.
Lemma lem174464 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174465 (m : nat) : (term91 m) = (term100 m).
Proof. exact (MK_COMB (@lem174464) (@lem174463 m)). Qed.
Lemma lem174466 : term92 = term101.
Proof. exact (fun_ext (fun m : nat => @lem174465 m)). Qed.
Lemma lem174467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174524 : term69 = term102.
Proof. exact (MK_COMB (@lem174467) (@lem174466)). Qed.
Lemma lem174525 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem174524) (@lem174417 h1)). Qed.
Lemma lem174547 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem174563 (n : nat) (p : nat) (h1 : term62 n p) : term62 n p.
Proof. exact (h1). Qed.
Lemma lem174576 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem174577 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem174576 n m)). Qed.
Lemma lem174578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174579 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem174578) (@lem174577 m)). Qed.
Lemma lem174580 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem174579 m)). Qed.
Lemma lem174581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174582 : term96 = term96.
Proof. exact (MK_COMB (@lem174581) (@lem174580)). Qed.
Lemma lem174583 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem174582) (@lem174455 h1)). Qed.
Lemma lem174606 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem174607 (m : nat) : (term99 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem174606 n m)). Qed.
Lemma lem174608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174609 (m : nat) : (term100 m) = (term100 m).
Proof. exact (MK_COMB (@lem174608) (@lem174607 m)). Qed.
Lemma lem174610 : term101 = term101.
Proof. exact (fun_ext (fun m : nat => @lem174609 m)). Qed.
Lemma lem174611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174612 : term102 = term102.
Proof. exact (MK_COMB (@lem174611) (@lem174610)). Qed.
Lemma lem174613 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem174612) (@lem174525 h1)). Qed.
Lemma lem174621 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem174625 (n : nat) (p : nat) (h1 : term62 n p) : term62 n p.
Proof. exact (h1). Qed.
Lemma lem174627 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem174628 (m : nat) : (term93 m) = (term93 m).
Proof. exact (fun_ext (fun n : nat => @lem174627 n m)). Qed.
Lemma lem174629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174630 (m : nat) : (term94 m) = (term94 m).
Proof. exact (MK_COMB (@lem174629) (@lem174628 m)). Qed.
Lemma lem174631 : term95 = term95.
Proof. exact (fun_ext (fun m : nat => @lem174630 m)). Qed.
Lemma lem174632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174634 : term96 = term96.
Proof. exact (MK_COMB (@lem174632) (@lem174631)). Qed.
Lemma lem174635 (h1 : term96) : term96.
Proof. exact (EQ_MP (@lem174634) (@lem174583 h1)). Qed.
Lemma lem174643 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem174644 (m : nat) : (term99 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem174643 n m)). Qed.
Lemma lem174645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174646 (m : nat) : (term100 m) = (term100 m).
Proof. exact (MK_COMB (@lem174645) (@lem174644 m)). Qed.
Lemma lem174647 : term101 = term101.
Proof. exact (fun_ext (fun m : nat => @lem174646 m)). Qed.
Lemma lem174648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem174650 : term102 = term102.
Proof. exact (MK_COMB (@lem174648) (@lem174647)). Qed.
Lemma lem174651 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem174650) (@lem174613 h1)). Qed.
Lemma lem174652 (_3651 : nat) (h1 : term96) : term103 _3651.
Proof. exact (@lem174635 h1 _3651). Qed.
Lemma lem174653 (_3651 : nat) : (term103 _3651) = (term94 _3651).
Proof. exact (eq_refl (term103 _3651)). Qed.
Lemma lem174654 (_3651 : nat) (h1 : term96) : term94 _3651.
Proof. exact (EQ_MP (@lem174653 _3651) (@lem174652 _3651 h1)). Qed.
Lemma lem174655 (_3651 : nat) (_3652 : nat) (h1 : term96) : term104 _3651 _3652.
Proof. exact (@lem174654 _3651 h1 _3652). Qed.
Lemma lem174656 (_3652 : nat) (_3651 : nat) : (term104 _3651 _3652) = ((Nat.add _3651 _3652) = (Nat.add _3652 _3651)).
Proof. exact (eq_refl (term104 _3651 _3652)). Qed.
Lemma lem174658 (_3653 : nat) (h1 : term69) : term105 _3653.
Proof. exact (@lem174651 h1 _3653). Qed.
Lemma lem174659 (_3653 : nat) : (term105 _3653) = (term100 _3653).
Proof. exact (eq_refl (term105 _3653)). Qed.
Lemma lem174660 (_3653 : nat) (h1 : term69) : term100 _3653.
Proof. exact (EQ_MP (@lem174659 _3653) (@lem174658 _3653 h1)). Qed.
Lemma lem174661 (_3653 : nat) (_3654 : nat) (h1 : term69) : term106 _3653 _3654.
Proof. exact (@lem174660 _3653 h1 _3654). Qed.
Lemma lem174662 (_3654 : nat) (_3653 : nat) : (term106 _3653 _3654) = (term97 _3654 _3653).
Proof. exact (eq_refl (term106 _3653 _3654)). Qed.
Lemma lem174667 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem174669 (n : nat) (p : nat) (h1 : term62 n p) : term62 n p.
Proof. exact (h1). Qed.
Lemma lem174677 (_3654 : nat) (_3653 : nat) (h1 : term69) : term97 _3654 _3653.
Proof. exact (EQ_MP (@lem174662 _3654 _3653) (@lem174661 _3653 _3654 h1)). Qed.
Lemma lem174786 (x : nat) (y : nat) (z : nat) : term107 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem174788 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem174789 (p : nat) (n : nat) (h1 : Peano.le p n) : term108 p n.
Proof. exact (fun h0 : term109 p n => @lem174788 p n h1). Qed.
Lemma lem174791 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem174792 (p : nat) (n : nat) : (term108 p n) = (Peano.le p n).
Proof. exact (@lem174791 (Peano.le p n)). Qed.
Lemma lem174793 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (EQ_MP (@lem174792 p n) (@lem174789 p n h1)). Qed.
Lemma lem174799 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem174800 (_3654 : nat) (_3653 : nat) : (term97 _3654 _3653) = (term111 _3654 _3653).
Proof. exact (@lem174799 ((term98 _3653 _3654) = _3653) (term109 _3654 _3653)). Qed.
Lemma lem174808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem174809 (_3654 : nat) (_3653 : nat) : (term112 _3654 _3653) = (term113 _3654 _3653).
Proof. exact (MK_COMB (@lem174808) (@lem174800 _3654 _3653)). Qed.
Lemma lem174817 (_3654 : nat) (_3653 : nat) : (term111 _3654 _3653) = (term111 _3654 _3653).
Proof. exact (eq_refl (term111 _3654 _3653)). Qed.
Lemma lem174818 (_3654 : nat) (_3653 : nat) : ((term97 _3654 _3653) = (term111 _3654 _3653)) = ((term111 _3654 _3653) = (term111 _3654 _3653)).
Proof. exact (MK_COMB (@lem174809 _3654 _3653) (@lem174817 _3654 _3653)). Qed.
Lemma lem174820 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem174821 (x : Prop) : (x = x) = True.
Proof. exact (@lem174820 Prop x). Qed.
Lemma lem174822 (_3654 : nat) (_3653 : nat) : ((term111 _3654 _3653) = (term111 _3654 _3653)) = True.
Proof. exact (@lem174821 (term111 _3654 _3653)). Qed.
Lemma lem174823 (_3654 : nat) (_3653 : nat) : ((term97 _3654 _3653) = (term111 _3654 _3653)) = True.
Proof. exact (TRANS (@lem174818 _3654 _3653) (@lem174822 _3654 _3653)). Qed.
Lemma lem174824 (_3654 : nat) (_3653 : nat) : True = ((term97 _3654 _3653) = (term111 _3654 _3653)).
Proof. exact (SYM (@lem174823 _3654 _3653)). Qed.
Lemma lem174825 (_3654 : nat) (_3653 : nat) : (term97 _3654 _3653) = (term111 _3654 _3653).
Proof. exact (EQ_MP (@lem174824 _3654 _3653) (@lem0)). Qed.
Lemma lem174826 (_3654 : nat) (_3653 : nat) (h1 : term69) : term111 _3654 _3653.
Proof. exact (EQ_MP (@lem174825 _3654 _3653) (@lem174677 _3654 _3653 h1)). Qed.
Lemma lem174828 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem174829 (_3654 : nat) (_3653 : nat) : (term111 _3654 _3653) = (term115 _3654 _3653).
Proof. exact (@lem174828 (term109 _3654 _3653) ((term98 _3653 _3654) = _3653)). Qed.
Lemma lem174831 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem174832 (_3654 : nat) (_3653 : nat) : (term117 _3654 _3653) = (Peano.le _3654 _3653).
Proof. exact (@lem174831 (Peano.le _3654 _3653)). Qed.
Lemma lem174833 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem174834 (_3654 : nat) (_3653 : nat) : (term118 _3654 _3653) = (term76 _3654 _3653).
Proof. exact (MK_COMB (@lem174833) (@lem174832 _3654 _3653)). Qed.
Lemma lem174835 (_3654 : nat) (_3653 : nat) : ((term98 _3653 _3654) = _3653) = ((term98 _3653 _3654) = _3653).
Proof. exact (eq_refl ((term98 _3653 _3654) = _3653)). Qed.
Lemma lem174836 (_3654 : nat) (_3653 : nat) : (term115 _3654 _3653) = (term89 _3654 _3653).
Proof. exact (MK_COMB (@lem174834 _3654 _3653) (@lem174835 _3654 _3653)). Qed.
Lemma lem174837 (_3654 : nat) (_3653 : nat) : (term111 _3654 _3653) = (term89 _3654 _3653).
Proof. exact (TRANS (@lem174829 _3654 _3653) (@lem174836 _3654 _3653)). Qed.
Lemma lem174840 (_3654 : nat) (_3653 : nat) (h1 : term69) : term89 _3654 _3653.
Proof. exact (EQ_MP (@lem174837 _3654 _3653) (@lem174826 _3654 _3653 h1)). Qed.
Lemma lem174841 (p : nat) (n : nat) (h1 : term69) : term89 p n.
Proof. exact (@lem174840 p n h1). Qed.
Lemma lem174844 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : (term98 n p) = n.
Proof. exact (@lem174841 p n h1 (@lem174793 p n h2)). Qed.
Lemma lem174845 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : term119 p n.
Proof. exact (fun h0 : term120 p n => @lem174844 p n h1 h2). Qed.
Lemma lem174847 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem174848 (p : nat) (n : nat) : (term119 p n) = ((term98 n p) = n).
Proof. exact (@lem174847 ((term98 n p) = n)). Qed.
Lemma lem174849 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : (term98 n p) = n.
Proof. exact (EQ_MP (@lem174848 p n) (@lem174845 p n h1 h2)). Qed.
Lemma lem174851 (_3652 : nat) (_3651 : nat) (h1 : term96) : (Nat.add _3651 _3652) = (Nat.add _3652 _3651).
Proof. exact (EQ_MP (@lem174656 _3652 _3651) (@lem174655 _3651 _3652 h1)). Qed.
Lemma lem174852 (n : nat) (p : nat) (h1 : term96) : (term98 n p) = (term59 n p).
Proof. exact (@lem174851 p (Nat.sub n p) h1). Qed.
Lemma lem174853 (n : nat) (p : nat) (h1 : term96) : term121 n p.
Proof. exact (fun h0 : term122 n p => @lem174852 n p h1). Qed.
Lemma lem174855 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem174856 (n : nat) (p : nat) : (term121 n p) = ((term98 n p) = (term59 n p)).
Proof. exact (@lem174855 ((term98 n p) = (term59 n p))). Qed.
Lemma lem174857 (n : nat) (p : nat) (h1 : term96) : (term98 n p) = (term59 n p).
Proof. exact (EQ_MP (@lem174856 n p) (@lem174853 n p h1)). Qed.
Lemma lem174875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem174876 (y : nat) (x : nat) (z : nat) : (term123 x y z) = (term124 y x z).
Proof. exact (@lem174875 (y = z) (term125 x z)). Qed.
Lemma lem174886 (x : nat) (y : nat) : (term126 x y) = (term126 x y).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem174887 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term127 y x z).
Proof. exact (MK_COMB (@lem174886 x y) (@lem174876 y x z)). Qed.
Lemma lem174891 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem174892 (y : nat) (x : nat) (z : nat) : (term127 y x z) = (term129 y x z).
Proof. exact (@lem174891 (y = z) (term125 x y) (term125 x z)). Qed.
Lemma lem174914 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term129 y x z).
Proof. exact (TRANS (@lem174887 y x z) (@lem174892 y x z)). Qed.
Lemma lem174915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem174916 (y : nat) (x : nat) (z : nat) : (term130 x y z) = (term131 y x z).
Proof. exact (MK_COMB (@lem174915) (@lem174914 y x z)). Qed.
Lemma lem174938 (y : nat) (x : nat) (z : nat) : (term129 y x z) = (term129 y x z).
Proof. exact (eq_refl (term129 y x z)). Qed.
Lemma lem174939 (y : nat) (x : nat) (z : nat) : ((term107 x y z) = (term129 y x z)) = ((term129 y x z) = (term129 y x z)).
Proof. exact (MK_COMB (@lem174916 y x z) (@lem174938 y x z)). Qed.
Lemma lem174941 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem174942 (x : Prop) : (x = x) = True.
Proof. exact (@lem174941 Prop x). Qed.
Lemma lem174943 (y : nat) (x : nat) (z : nat) : ((term129 y x z) = (term129 y x z)) = True.
Proof. exact (@lem174942 (term129 y x z)). Qed.
Lemma lem174944 (y : nat) (x : nat) (z : nat) : ((term107 x y z) = (term129 y x z)) = True.
Proof. exact (TRANS (@lem174939 y x z) (@lem174943 y x z)). Qed.
Lemma lem174945 (y : nat) (x : nat) (z : nat) : True = ((term107 x y z) = (term129 y x z)).
Proof. exact (SYM (@lem174944 y x z)). Qed.
Lemma lem174946 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term129 y x z).
Proof. exact (EQ_MP (@lem174945 y x z) (@lem0)). Qed.
Lemma lem174947 (y : nat) (x : nat) (z : nat) : term129 y x z.
Proof. exact (EQ_MP (@lem174946 y x z) (@lem174786 x y z)). Qed.
Lemma lem174949 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem174950 (x : nat) (y : nat) (z : nat) : (term129 y x z) = (term132 x y z).
Proof. exact (@lem174949 (term133 y x z) (y = z)). Qed.
Lemma lem174952 (a : Prop) (b : Prop) : (term134 a b) = (term135 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem174953 (y : nat) (x : nat) (z : nat) : (term136 y x z) = (term137 y x z).
Proof. exact (@lem174952 (term125 x y) (term125 x z)). Qed.
Lemma lem174955 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem174956 (x : nat) (y : nat) : (term138 x y) = (x = y).
Proof. exact (@lem174955 (x = y)). Qed.
Lemma lem174957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem174958 (x : nat) (y : nat) : (term139 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem174957) (@lem174956 x y)). Qed.
Lemma lem174960 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem174961 (x : nat) (z : nat) : (term138 x z) = (x = z).
Proof. exact (@lem174960 (x = z)). Qed.
Lemma lem174962 (y : nat) (x : nat) (z : nat) : (term137 y x z) = (term141 y x z).
Proof. exact (MK_COMB (@lem174958 x y) (@lem174961 x z)). Qed.
Lemma lem174963 (y : nat) (x : nat) (z : nat) : (term136 y x z) = (term141 y x z).
Proof. exact (TRANS (@lem174953 y x z) (@lem174962 y x z)). Qed.
Lemma lem174964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem174965 (y : nat) (x : nat) (z : nat) : (term142 y x z) = (term143 y x z).
Proof. exact (MK_COMB (@lem174964) (@lem174963 y x z)). Qed.
Lemma lem174966 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem174967 (x : nat) (y : nat) (z : nat) : (term132 x y z) = (term144 x y z).
Proof. exact (MK_COMB (@lem174965 y x z) (@lem174966 y z)). Qed.
Lemma lem174968 (x : nat) (y : nat) (z : nat) : (term129 y x z) = (term144 x y z).
Proof. exact (TRANS (@lem174950 x y z) (@lem174967 x y z)). Qed.
Lemma lem174970 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : Peano.le p n) : term145 n p.
Proof. exact (conj (@lem174849 p n h2 h3) (@lem174857 n p h1)). Qed.
Lemma lem174972 (x : nat) (y : nat) (z : nat) : term144 x y z.
Proof. exact (EQ_MP (@lem174968 x y z) (@lem174947 y x z)). Qed.
Lemma lem174973 (n : nat) (p : nat) : term146 n p.
Proof. exact (@lem174972 (term98 n p) n (term59 n p)). Qed.
Lemma lem174976 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : Peano.le p n) : n = (term59 n p).
Proof. exact (@lem174973 n p (@lem174970 p n h1 h2 h3)). Qed.
Lemma lem174977 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : Peano.le p n) : term147 n p.
Proof. exact (fun h0 : term62 n p => @lem174976 p n h1 h2 h3). Qed.
Lemma lem174979 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem174980 (n : nat) (p : nat) : (term147 n p) = (n = (term59 n p)).
Proof. exact (@lem174979 (n = (term59 n p))). Qed.
Lemma lem174981 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : Peano.le p n) : n = (term59 n p).
Proof. exact (EQ_MP (@lem174980 n p) (@lem174977 p n h1 h2 h3)). Qed.
Lemma lem174984 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem174986 (n : nat) (p : nat) : (term62 n p) = (term148 n p).
Proof. exact (@lem174984 (n = (term59 n p))). Qed.
Lemma lem174989 (n : nat) (p : nat) (h1 : term62 n p) : term148 n p.
Proof. exact (EQ_MP (@lem174986 n p) (@lem174669 n p h1)). Qed.
Lemma lem174992 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (@lem174989 n p h3 (@lem174981 p n h1 h2 h4)). Qed.
Lemma lem174993 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : term149.
Proof. exact (fun h0 : ~ False => @lem174992 p n h1 h2 h3 h4). Qed.
Lemma lem174995 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem174996 : term149 = False.
Proof. exact (@lem174995 False). Qed.
Lemma lem174997 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem174996) (@lem174993 p n h1 h2 h3 h4)). Qed.
Lemma lem174998 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (term62 n p) = False.
Proof. exact (prop_ext (fun h5 : term62 n p => @lem174997 p n h1 h2 h3 h4) (fun h5 : False => @lem174669 n p h3)). Qed.
Lemma lem174999 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem174998 p n h1 h2 h3 h4) (@lem174669 n p h3)). Qed.
Lemma lem175000 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p n => @lem174999 p n h1 h2 h3 h4) (fun h5 : False => @lem174667 p n h4)). Qed.
Lemma lem175001 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175000 p n h1 h2 h3 h4) (@lem174667 p n h4)). Qed.
Lemma lem175002 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (term62 n p) = False.
Proof. exact (prop_ext (fun h5 : term62 n p => @lem175001 p n h1 h2 h3 h4) (fun h5 : False => @lem174625 n p h3)). Qed.
Lemma lem175003 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175002 p n h1 h2 h3 h4) (@lem174625 n p h3)). Qed.
Lemma lem175004 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p n => @lem175003 p n h1 h2 h3 h4) (fun h5 : False => @lem174621 p n h4)). Qed.
Lemma lem175005 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175004 p n h1 h2 h3 h4) (@lem174621 p n h4)). Qed.
Lemma lem175006 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem175005 p n h1 h2 h3 h4) (fun h5 : False => @lem174635 h1)). Qed.
Lemma lem175007 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175006 p n h1 h2 h3 h4) (@lem174635 h1)). Qed.
Lemma lem175008 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (term62 n p) = False.
Proof. exact (prop_ext (fun h5 : term62 n p => @lem175007 p n h1 h2 h3 h4) (fun h5 : False => @lem174625 n p h3)). Qed.
Lemma lem175009 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175008 p n h1 h2 h3 h4) (@lem174625 n p h3)). Qed.
Lemma lem175010 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p n => @lem175009 p n h1 h2 h3 h4) (fun h5 : False => @lem174621 p n h4)). Qed.
Lemma lem175011 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175010 p n h1 h2 h3 h4) (@lem174621 p n h4)). Qed.
Lemma lem175012 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem175011 p n h1 h2 h3 h4) (fun h5 : False => @lem174583 h1)). Qed.
Lemma lem175013 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175012 p n h1 h2 h3 h4) (@lem174583 h1)). Qed.
Lemma lem175014 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (term62 n p) = False.
Proof. exact (prop_ext (fun h5 : term62 n p => @lem175013 p n h1 h2 h3 h4) (fun h5 : False => @lem174563 n p h3)). Qed.
Lemma lem175015 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175014 p n h1 h2 h3 h4) (@lem174563 n p h3)). Qed.
Lemma lem175016 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p n => @lem175015 p n h1 h2 h3 h4) (fun h5 : False => @lem174547 p n h4)). Qed.
Lemma lem175017 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175016 p n h1 h2 h3 h4) (@lem174547 p n h4)). Qed.
Lemma lem175018 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : term96 = False.
Proof. exact (prop_ext (fun h5 : term96 => @lem175017 p n h1 h2 h3 h4) (fun h5 : False => @lem174455 h1)). Qed.
Lemma lem175019 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175018 p n h1 h2 h3 h4) (@lem174455 h1)). Qed.
Lemma lem175020 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (term62 n p) = False.
Proof. exact (prop_ext (fun h5 : term62 n p => @lem175019 p n h1 h2 h3 h4) (fun h5 : False => @lem174435 n p h3)). Qed.
Lemma lem175021 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175020 p n h1 h2 h3 h4) (@lem174435 n p h3)). Qed.
Lemma lem175022 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le p n => @lem175021 p n h1 h2 h3 h4) (fun h5 : False => @lem174429 p n h4)). Qed.
Lemma lem175023 (p : nat) (n : nat) (h1 : term96) (h2 : term69) (h3 : term62 n p) (h4 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem175022 p n h1 h2 h3 h4) (@lem174429 p n h4)). Qed.
Lemma lem175024 (p : nat) (n : nat) (h1 : term96) (h2 : term62 n p) (h3 : Peano.le p n) : term67.
Proof. exact (fun h0 : term69 => @lem175023 p n h1 h0 h2 h3). Qed.
Lemma lem175025 : term67 = term68.
Proof. exact (@lem69 term69). Qed.
Lemma lem175026 (p : nat) (n : nat) (h1 : term96) (h2 : term62 n p) (h3 : Peano.le p n) : term68.
Proof. exact (EQ_MP (@lem175025) (@lem175024 p n h1 h2 h3)). Qed.
Lemma lem175027 (p : nat) (n : nat) (h1 : term62 n p) (h2 : Peano.le p n) : term72.
Proof. exact (fun h0 : term96 => @lem175026 p n h0 h1 h2). Qed.
Lemma lem175028 (p : nat) (n : nat) (h1 : Peano.le p n) : term75 n p.
Proof. exact (fun h0 : term62 n p => @lem175027 p n h0 h1). Qed.
Lemma lem175029 (n : nat) (p : nat) : term78 n p.
Proof. exact (fun h0 : Peano.le p n => @lem175028 p n h0). Qed.
Lemma lem175030 (n : nat) (p : nat) : term80 n p.
Proof. exact (fun h0 : term30 n p => @lem175029 n p). Qed.
Lemma lem175035 (p : nat) : term84 p.
Proof. exact (fun n : nat => @lem175030 n p). Qed.
Lemma lem175040 : term88.
Proof. exact (fun p : nat => @lem175035 p). Qed.
Lemma lem175041 : term87.
Proof. exact (EQ_MP (@lem174412) (@lem175040)). Qed.
Lemma lem175042 (p : nat) : term150 p.
Proof. exact (@lem175041 p). Qed.
Lemma lem175043 (p : nat) : (term150 p) = (term83 p).
Proof. exact (eq_refl (term150 p)). Qed.
Lemma lem175044 (p : nat) : term83 p.
Proof. exact (EQ_MP (@lem175043 p) (@lem175042 p)). Qed.
Lemma lem175045 (p : nat) (n : nat) : term151 p n.
Proof. exact (@lem175044 p n). Qed.
Lemma lem175046 (n : nat) (p : nat) : (term151 p n) = (term63 n p).
Proof. exact (eq_refl (term151 p n)). Qed.
Lemma lem175047 (n : nat) (p : nat) : term63 n p.
Proof. exact (EQ_MP (@lem175046 n p) (@lem175045 p n)). Qed.
Lemma lem175049 (n : nat) (p : nat) : term63 n p.
Proof. exact (@lem174248 n p (@lem175047 n p)). Qed.
Lemma lem175050 (n : nat) (p : nat) (h1 : term30 n p) : term77 n p.
Proof. exact (@lem175049 n p (@lem174210 n p h1)). Qed.
Lemma lem175051 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term74 n p.
Proof. exact (@lem175050 n p h2 (@lem174214 n p h1)). Qed.
Lemma lem175052 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term62 n p) (h3 : term30 n p) : term71.
Proof. exact (@lem175051 n p h1 h3 (@lem174233 n p h2)). Qed.
Lemma lem175053 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term62 n p) (h3 : term30 n p) : term67.
Proof. exact (@lem175052 n p h1 h2 h3 (@lem77775)). Qed.
Lemma lem175054 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term62 n p) (h3 : term30 n p) : False.
Proof. exact (@lem175053 n p h1 h2 h3 (@lem136494)). Qed.
Lemma lem175055 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term62 n p) (h3 : term30 n p) : (term62 n p) = False.
Proof. exact (prop_ext (fun h4 : term62 n p => @lem175054 n p h1 h2 h3) (fun h4 : False => @lem174233 n p h2)). Qed.
Lemma lem175056 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term62 n p) (h3 : term30 n p) : False.
Proof. exact (EQ_MP (@lem175055 n p h1 h2 h3) (@lem174233 n p h2)). Qed.
Lemma lem175057 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term61 n p.
Proof. exact (fun h0 : term62 n p => @lem175056 n p h1 h0 h2). Qed.
Lemma lem175058 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : n = (term59 n p).
Proof. exact (EQ_MP (@lem174232 n p) (@lem175057 n p h1 h2)). Qed.
Lemma lem175059 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : n = (term58 n p).
Proof. exact (EQ_MP (@lem174228 n p) (@lem175058 n p h1 h2)). Qed.
Lemma lem175061 (p : Prop) : p = (term60 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem175062 (n : nat) (p : nat) : (term152 n p) = (term153 n p).
Proof. exact (@lem175061 (term152 n p)). Qed.
Lemma lem175063 (n : nat) (p : nat) : (term153 n p) = (term152 n p).
Proof. exact (SYM (@lem175062 n p)). Qed.
Lemma lem175064 (n : nat) (p : nat) (h1 : term154 n p) : term154 n p.
Proof. exact (h1). Qed.
Lemma lem175067 (n : nat) (p : nat) (h1 : term155 n p) : term155 n p.
Proof. exact (h1). Qed.
Lemma lem175068 (n : nat) (p : nat) : term156 n p.
Proof. exact (fun h0 : term155 n p => @lem175067 n p h0). Qed.
Lemma lem175069 (n : nat) (p : nat) (h1 : term156 n p) : term156 n p.
Proof. exact (h1). Qed.
Lemma lem175070 (n : nat) (p : nat) (h1 : term155 n p) : term155 n p.
Proof. exact (h1). Qed.
Lemma lem175071 (n : nat) (p : nat) (h1 : term155 n p) (h2 : term156 n p) : term155 n p.
Proof. exact (@lem175069 n p h2 (@lem175070 n p h1)). Qed.
Lemma lem175072 (n : nat) (p : nat) (h1 : term155 n p) : term157 n p.
Proof. exact (fun h0 : term156 n p => @lem175071 n p h1 h0). Qed.
Lemma lem175073 (n : nat) (p : nat) (h1 : term156 n p) : term156 n p.
Proof. exact (h1). Qed.
Lemma lem175074 (n : nat) (p : nat) (h1 : term155 n p) (h2 : term156 n p) : term155 n p.
Proof. exact (@lem175072 n p h1 (@lem175073 n p h2)). Qed.
Lemma lem175075 (n : nat) (p : nat) (h1 : term156 n p) : term156 n p.
Proof. exact (fun h0 : term155 n p => @lem175074 n p h0 h1). Qed.
Lemma lem175076 (n : nat) (p : nat) : term158 n p.
Proof. exact (fun h0 : term156 n p => @lem175075 n p h0). Qed.
Lemma lem175079 (n : nat) (p : nat) : term156 n p.
Proof. exact (@lem175076 n p (@lem175068 n p)). Qed.
Lemma lem175135 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem175136 : term159 = term160.
Proof. exact (@lem175135 term161). Qed.
Lemma lem175149 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem175150 : term163 = term164.
Proof. exact (MK_COMB (@lem175149) (@lem175136)). Qed.
Lemma lem175153 : term165 = term165.
Proof. exact (eq_refl term165). Qed.
Lemma lem175154 : term166 = term167.
Proof. exact (MK_COMB (@lem175153) (@lem175150)). Qed.
Lemma lem175157 : term168 = term168.
Proof. exact (eq_refl term168). Qed.
Lemma lem175158 : term169 = term170.
Proof. exact (MK_COMB (@lem175157) (@lem175154)). Qed.
Lemma lem175161 (n : nat) (p : nat) : (term171 n p) = (term171 n p).
Proof. exact (eq_refl (term171 n p)). Qed.
Lemma lem175162 (n : nat) (p : nat) : (term172 n p) = (term173 n p).
Proof. exact (MK_COMB (@lem175161 n p) (@lem175158)). Qed.
Lemma lem175165 (p : nat) (n : nat) : (term76 p n) = (term76 p n).
Proof. exact (eq_refl (term76 p n)). Qed.
Lemma lem175166 (n : nat) (p : nat) : (term174 n p) = (term175 n p).
Proof. exact (MK_COMB (@lem175165 p n) (@lem175162 n p)). Qed.
Lemma lem175169 (n : nat) (p : nat) : (term79 n p) = (term79 n p).
Proof. exact (eq_refl (term79 n p)). Qed.
Lemma lem175170 (n : nat) (p : nat) : (term155 n p) = (term176 n p).
Proof. exact (MK_COMB (@lem175169 n p) (@lem175166 n p)). Qed.
Lemma lem175173 (p : nat) : (term177 p) = (term178 p).
Proof. exact (fun_ext (fun n : nat => @lem175170 n p)). Qed.
Lemma lem175174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175175 (p : nat) : (term179 p) = (term180 p).
Proof. exact (MK_COMB (@lem175174) (@lem175173 p)). Qed.
Lemma lem175180 : term181 = term182.
Proof. exact (fun_ext (fun p : nat => @lem175175 p)). Qed.
Lemma lem175181 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175190 : term183 = term184.
Proof. exact (MK_COMB (@lem175181) (@lem175180)). Qed.
Lemma lem175195 (p : nat) (m : nat) (n : nat) : ((term185 m n p) = (Peano.lt m n)) = ((term185 m n p) = (Peano.lt m n)).
Proof. exact (eq_refl ((term185 m n p) = (Peano.lt m n))). Qed.
Lemma lem175196 (m : nat) (n : nat) : (term186 m n) = (term186 m n).
Proof. exact (fun_ext (fun p : nat => @lem175195 p m n)). Qed.
Lemma lem175197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175198 (m : nat) (n : nat) : (term187 m n) = (term187 m n).
Proof. exact (MK_COMB (@lem175197) (@lem175196 m n)). Qed.
Lemma lem175199 (m : nat) : (term188 m) = (term188 m).
Proof. exact (fun_ext (fun n : nat => @lem175198 m n)). Qed.
Lemma lem175200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175201 (m : nat) : (term189 m) = (term189 m).
Proof. exact (MK_COMB (@lem175200) (@lem175199 m)). Qed.
Lemma lem175202 : term190 = term190.
Proof. exact (fun_ext (fun m : nat => @lem175201 m)). Qed.
Lemma lem175203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175204 : term161 = term161.
Proof. exact (MK_COMB (@lem175203) (@lem175202)). Qed.
Lemma lem175205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem175206 : term160 = term160.
Proof. exact (MK_COMB (@lem175205) (@lem175204)). Qed.
Lemma lem175211 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem175212 (m : nat) : (term90 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem175211 n m)). Qed.
Lemma lem175213 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175214 (m : nat) : (term91 m) = (term91 m).
Proof. exact (MK_COMB (@lem175213) (@lem175212 m)). Qed.
Lemma lem175215 : term92 = term92.
Proof. exact (fun_ext (fun m : nat => @lem175214 m)). Qed.
Lemma lem175216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175217 : term69 = term69.
Proof. exact (MK_COMB (@lem175216) (@lem175215)). Qed.
Lemma lem175218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem175219 : term162 = term162.
Proof. exact (MK_COMB (@lem175218) (@lem175217)). Qed.
Lemma lem175220 : term164 = term164.
Proof. exact (MK_COMB (@lem175219) (@lem175206)). Qed.
Lemma lem175221 (n : nat) : ((term191 n) = (Nat.add n n)) = ((term191 n) = (Nat.add n n)).
Proof. exact (eq_refl ((term191 n) = (Nat.add n n))). Qed.
Lemma lem175222 : term192 = term192.
Proof. exact (fun_ext (fun n : nat => @lem175221 n)). Qed.
Lemma lem175223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175224 : term193 = term193.
Proof. exact (MK_COMB (@lem175223) (@lem175222)). Qed.
Lemma lem175225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem175226 : term165 = term165.
Proof. exact (MK_COMB (@lem175225) (@lem175224)). Qed.
Lemma lem175227 : term167 = term167.
Proof. exact (MK_COMB (@lem175226) (@lem175220)). Qed.
Lemma lem175236 (m : nat) (n : nat) (p : nat) (q : nat) : (term194 m n p q) = (term194 m n p q).
Proof. exact (eq_refl (term194 m n p q)). Qed.
Lemma lem175237 (m : nat) (n : nat) (p : nat) : (term195 m n p) = (term195 m n p).
Proof. exact (fun_ext (fun q : nat => @lem175236 m n p q)). Qed.
Lemma lem175238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175239 (m : nat) (n : nat) (p : nat) : (term196 m n p) = (term196 m n p).
Proof. exact (MK_COMB (@lem175238) (@lem175237 m n p)). Qed.
Lemma lem175240 (m : nat) (n : nat) : (term197 m n) = (term197 m n).
Proof. exact (fun_ext (fun p : nat => @lem175239 m n p)). Qed.
Lemma lem175241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175242 (m : nat) (n : nat) : (term198 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem175241) (@lem175240 m n)). Qed.
Lemma lem175243 (m : nat) : (term199 m) = (term199 m).
Proof. exact (fun_ext (fun n : nat => @lem175242 m n)). Qed.
Lemma lem175244 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175245 (m : nat) : (term200 m) = (term200 m).
Proof. exact (MK_COMB (@lem175244) (@lem175243 m)). Qed.
Lemma lem175246 : term201 = term201.
Proof. exact (fun_ext (fun m : nat => @lem175245 m)). Qed.
Lemma lem175247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175248 : term202 = term202.
Proof. exact (MK_COMB (@lem175247) (@lem175246)). Qed.
Lemma lem175249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem175250 : term168 = term168.
Proof. exact (MK_COMB (@lem175249) (@lem175248)). Qed.
Lemma lem175251 : term170 = term170.
Proof. exact (MK_COMB (@lem175250) (@lem175227)). Qed.
Lemma lem175256 (n : nat) (p : nat) : (term171 n p) = (term171 n p).
Proof. exact (eq_refl (term171 n p)). Qed.
Lemma lem175257 (n : nat) (p : nat) : (term173 n p) = (term173 n p).
Proof. exact (MK_COMB (@lem175256 n p) (@lem175251)). Qed.
Lemma lem175260 (p : nat) (n : nat) : (term76 p n) = (term76 p n).
Proof. exact (eq_refl (term76 p n)). Qed.
Lemma lem175261 (n : nat) (p : nat) : (term175 n p) = (term175 n p).
Proof. exact (MK_COMB (@lem175260 p n) (@lem175257 n p)). Qed.
Lemma lem175264 (n : nat) (p : nat) : (term79 n p) = (term79 n p).
Proof. exact (eq_refl (term79 n p)). Qed.
Lemma lem175265 (n : nat) (p : nat) : (term176 n p) = (term176 n p).
Proof. exact (MK_COMB (@lem175264 n p) (@lem175261 n p)). Qed.
Lemma lem175266 (p : nat) : (term178 p) = (term178 p).
Proof. exact (fun_ext (fun n : nat => @lem175265 n p)). Qed.
Lemma lem175267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175268 (p : nat) : (term180 p) = (term180 p).
Proof. exact (MK_COMB (@lem175267) (@lem175266 p)). Qed.
Lemma lem175269 : term182 = term182.
Proof. exact (fun_ext (fun p : nat => @lem175268 p)). Qed.
Lemma lem175270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175271 : term184 = term184.
Proof. exact (MK_COMB (@lem175270) (@lem175269)). Qed.
Lemma lem175364 : term183 = term184.
Proof. exact (TRANS (@lem175190) (@lem175271)). Qed.
Lemma lem175365 : term184 = term183.
Proof. exact (SYM (@lem175364)). Qed.
Lemma lem175370 (h1 : term193) : term193.
Proof. exact (h1). Qed.
Lemma lem175371 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem175372 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem175378 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem175384 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem175390 (n : nat) (p : nat) (h1 : term154 n p) : term154 n p.
Proof. exact (h1). Qed.
Lemma lem175481 (n : nat) : ((term191 n) = (Nat.add n n)) = ((term191 n) = (Nat.add n n)).
Proof. exact (eq_refl ((term191 n) = (Nat.add n n))). Qed.
Lemma lem175482 : term192 = term192.
Proof. exact (fun_ext (fun n : nat => @lem175481 n)). Qed.
Lemma lem175483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175492 : term193 = term193.
Proof. exact (MK_COMB (@lem175483) (@lem175482)). Qed.
Lemma lem175493 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem175492) (@lem175370 h1)). Qed.
Lemma lem175500 (n : nat) (m : nat) : (term89 n m) = (term97 n m).
Proof. exact (@lem17265 (Peano.le n m) ((term98 m n) = m)). Qed.
Lemma lem175501 (m : nat) : (term90 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem175500 n m)). Qed.
Lemma lem175502 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175503 (m : nat) : (term91 m) = (term100 m).
Proof. exact (MK_COMB (@lem175502) (@lem175501 m)). Qed.
Lemma lem175504 : term92 = term101.
Proof. exact (fun_ext (fun m : nat => @lem175503 m)). Qed.
Lemma lem175505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175562 : term69 = term102.
Proof. exact (MK_COMB (@lem175505) (@lem175504)). Qed.
Lemma lem175563 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem175562) (@lem175371 h1)). Qed.
Lemma lem175578 (p : nat) (m : nat) (n : nat) : ((term185 m n p) = (Peano.lt m n)) = (term203 p m n).
Proof. exact (@lem17784 (term185 m n p) (Peano.lt m n)). Qed.
Lemma lem175579 (m : nat) (n : nat) : (term186 m n) = (term204 m n).
Proof. exact (fun_ext (fun p : nat => @lem175578 p m n)). Qed.
Lemma lem175580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175581 (m : nat) (n : nat) : (term187 m n) = (term205 m n).
Proof. exact (MK_COMB (@lem175580) (@lem175579 m n)). Qed.
Lemma lem175582 (m : nat) : (term188 m) = (term206 m).
Proof. exact (fun_ext (fun n : nat => @lem175581 m n)). Qed.
Lemma lem175583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175584 (m : nat) : (term189 m) = (term207 m).
Proof. exact (MK_COMB (@lem175583) (@lem175582 m)). Qed.
Lemma lem175585 : term190 = term208.
Proof. exact (fun_ext (fun m : nat => @lem175584 m)). Qed.
Lemma lem175586 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175587 : term161 = term209.
Proof. exact (MK_COMB (@lem175586) (@lem175585)). Qed.
Lemma lem175597 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem175598 (P : nat -> Prop) (Q : nat -> Prop) : (term212 P Q) = (term213 P Q).
Proof. exact (@lem175597 nat P Q). Qed.
Lemma lem175599 (m : nat) (n : nat) : (term214 m n) = (term215 m n).
Proof. exact (@lem175598 (term216 m n) (term217 m n)). Qed.
Lemma lem175600 (p : nat) (m : nat) (n : nat) : (term218 m n p) = (term219 p m n).
Proof. exact (eq_refl (term218 m n p)). Qed.
Lemma lem175601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175602 (p : nat) (m : nat) (n : nat) : (term220 m n p) = (term221 p m n).
Proof. exact (MK_COMB (@lem175601) (@lem175600 p m n)). Qed.
Lemma lem175603 (p : nat) (m : nat) (n : nat) : (term222 m n p) = (term223 p m n).
Proof. exact (eq_refl (term222 m n p)). Qed.
Lemma lem175604 (p : nat) (m : nat) (n : nat) : (term224 m n p) = (term203 p m n).
Proof. exact (MK_COMB (@lem175602 p m n) (@lem175603 p m n)). Qed.
Lemma lem175605 (m : nat) (n : nat) : (term225 m n) = (term204 m n).
Proof. exact (fun_ext (fun p : nat => @lem175604 p m n)). Qed.
Lemma lem175606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175607 (m : nat) (n : nat) : (term214 m n) = (term205 m n).
Proof. exact (MK_COMB (@lem175606) (@lem175605 m n)). Qed.
Lemma lem175608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem175609 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (MK_COMB (@lem175608) (@lem175607 m n)). Qed.
Lemma lem175610 (p : nat) (m : nat) (n : nat) : (term218 m n p) = (term219 p m n).
Proof. exact (eq_refl (term218 m n p)). Qed.
Lemma lem175611 (m : nat) (n : nat) : (term228 m n) = (term216 m n).
Proof. exact (fun_ext (fun p : nat => @lem175610 p m n)). Qed.
Lemma lem175612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175613 (m : nat) (n : nat) : (term229 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem175612) (@lem175611 m n)). Qed.
Lemma lem175614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175615 (m : nat) (n : nat) : (term231 m n) = (term232 m n).
Proof. exact (MK_COMB (@lem175614) (@lem175613 m n)). Qed.
Lemma lem175616 (p : nat) (m : nat) (n : nat) : (term222 m n p) = (term223 p m n).
Proof. exact (eq_refl (term222 m n p)). Qed.
Lemma lem175617 (m : nat) (n : nat) : (term233 m n) = (term217 m n).
Proof. exact (fun_ext (fun p : nat => @lem175616 p m n)). Qed.
Lemma lem175618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175619 (m : nat) (n : nat) : (term234 m n) = (term235 m n).
Proof. exact (MK_COMB (@lem175618) (@lem175617 m n)). Qed.
Lemma lem175620 (m : nat) (n : nat) : (term215 m n) = (term236 m n).
Proof. exact (MK_COMB (@lem175615 m n) (@lem175619 m n)). Qed.
Lemma lem175621 (m : nat) (n : nat) : ((term214 m n) = (term215 m n)) = ((term205 m n) = (term236 m n)).
Proof. exact (MK_COMB (@lem175609 m n) (@lem175620 m n)). Qed.
Lemma lem175622 (m : nat) (n : nat) : (term205 m n) = (term236 m n).
Proof. exact (EQ_MP (@lem175621 m n) (@lem175599 m n)). Qed.
Lemma lem175644 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem175645 (P : nat -> Prop) (Q : Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem175644 nat P Q). Qed.
Lemma lem175646 (m : nat) (n : nat) : (term241 m n) = (term242 m n).
Proof. exact (@lem175645 (term243 m n) (term8 m n)). Qed.
Lemma lem175647 (m : nat) (n : nat) (p : nat) : (term244 m n p) = (term185 m n p).
Proof. exact (eq_refl (term244 m n p)). Qed.
Lemma lem175648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem175649 (m : nat) (n : nat) (p : nat) : (term245 m n p) = (term246 m n p).
Proof. exact (MK_COMB (@lem175648) (@lem175647 m n p)). Qed.
Lemma lem175650 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem175651 (p : nat) (m : nat) (n : nat) : (term247 p m n) = (term219 p m n).
Proof. exact (MK_COMB (@lem175649 m n p) (@lem175650 m n)). Qed.
Lemma lem175652 (m : nat) (n : nat) : (term248 m n) = (term216 m n).
Proof. exact (fun_ext (fun p : nat => @lem175651 p m n)). Qed.
Lemma lem175653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175654 (m : nat) (n : nat) : (term241 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem175653) (@lem175652 m n)). Qed.
Lemma lem175655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem175656 (m : nat) (n : nat) : (term249 m n) = (term250 m n).
Proof. exact (MK_COMB (@lem175655) (@lem175654 m n)). Qed.
Lemma lem175657 (m : nat) (n : nat) (p : nat) : (term244 m n p) = (term185 m n p).
Proof. exact (eq_refl (term244 m n p)). Qed.
Lemma lem175658 (m : nat) (n : nat) : (term251 m n) = (term243 m n).
Proof. exact (fun_ext (fun p : nat => @lem175657 m n p)). Qed.
Lemma lem175659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175660 (m : nat) (n : nat) : (term252 m n) = (term253 m n).
Proof. exact (MK_COMB (@lem175659) (@lem175658 m n)). Qed.
Lemma lem175661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem175662 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (MK_COMB (@lem175661) (@lem175660 m n)). Qed.
Lemma lem175663 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem175664 (m : nat) (n : nat) : (term242 m n) = (term256 m n).
Proof. exact (MK_COMB (@lem175662 m n) (@lem175663 m n)). Qed.
Lemma lem175665 (m : nat) (n : nat) : ((term241 m n) = (term242 m n)) = ((term230 m n) = (term256 m n)).
Proof. exact (MK_COMB (@lem175656 m n) (@lem175664 m n)). Qed.
Lemma lem175666 (m : nat) (n : nat) : (term230 m n) = (term256 m n).
Proof. exact (EQ_MP (@lem175665 m n) (@lem175646 m n)). Qed.
Lemma lem175671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175672 (m : nat) (n : nat) : (term232 m n) = (term257 m n).
Proof. exact (MK_COMB (@lem175671) (@lem175666 m n)). Qed.
Lemma lem175694 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem175695 (P : nat -> Prop) (Q : Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem175694 nat P Q). Qed.
Lemma lem175696 (m : nat) (n : nat) : (term258 m n) = (term259 m n).
Proof. exact (@lem175695 (term260 m n) (Peano.lt m n)). Qed.
Lemma lem175697 (m : nat) (n : nat) (p : nat) : (term261 m n p) = (term262 m n p).
Proof. exact (eq_refl (term261 m n p)). Qed.
Lemma lem175698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem175699 (m : nat) (n : nat) (p : nat) : (term263 m n p) = (term264 m n p).
Proof. exact (MK_COMB (@lem175698) (@lem175697 m n p)). Qed.
Lemma lem175700 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem175701 (p : nat) (m : nat) (n : nat) : (term265 p m n) = (term223 p m n).
Proof. exact (MK_COMB (@lem175699 m n p) (@lem175700 m n)). Qed.
Lemma lem175702 (m : nat) (n : nat) : (term266 m n) = (term217 m n).
Proof. exact (fun_ext (fun p : nat => @lem175701 p m n)). Qed.
Lemma lem175703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175704 (m : nat) (n : nat) : (term258 m n) = (term235 m n).
Proof. exact (MK_COMB (@lem175703) (@lem175702 m n)). Qed.
Lemma lem175705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem175706 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (MK_COMB (@lem175705) (@lem175704 m n)). Qed.
Lemma lem175707 (m : nat) (n : nat) (p : nat) : (term261 m n p) = (term262 m n p).
Proof. exact (eq_refl (term261 m n p)). Qed.
Lemma lem175708 (m : nat) (n : nat) : (term269 m n) = (term260 m n).
Proof. exact (fun_ext (fun p : nat => @lem175707 m n p)). Qed.
Lemma lem175709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175710 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem175709) (@lem175708 m n)). Qed.
Lemma lem175711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem175712 (m : nat) (n : nat) : (term272 m n) = (term273 m n).
Proof. exact (MK_COMB (@lem175711) (@lem175710 m n)). Qed.
Lemma lem175713 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem175714 (m : nat) (n : nat) : (term259 m n) = (term274 m n).
Proof. exact (MK_COMB (@lem175712 m n) (@lem175713 m n)). Qed.
Lemma lem175715 (m : nat) (n : nat) : ((term258 m n) = (term259 m n)) = ((term235 m n) = (term274 m n)).
Proof. exact (MK_COMB (@lem175706 m n) (@lem175714 m n)). Qed.
Lemma lem175716 (m : nat) (n : nat) : (term235 m n) = (term274 m n).
Proof. exact (EQ_MP (@lem175715 m n) (@lem175696 m n)). Qed.
Lemma lem175721 (m : nat) (n : nat) : (term236 m n) = (term275 m n).
Proof. exact (MK_COMB (@lem175672 m n) (@lem175716 m n)). Qed.
Lemma lem175722 (m : nat) (n : nat) : (term205 m n) = (term275 m n).
Proof. exact (TRANS (@lem175622 m n) (@lem175721 m n)). Qed.
Lemma lem175723 (m : nat) : (term206 m) = (term276 m).
Proof. exact (fun_ext (fun n : nat => @lem175722 m n)). Qed.
Lemma lem175724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175725 (m : nat) : (term207 m) = (term277 m).
Proof. exact (MK_COMB (@lem175724) (@lem175723 m)). Qed.
Lemma lem175727 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem175728 (P : nat -> Prop) (Q : nat -> Prop) : (term212 P Q) = (term213 P Q).
Proof. exact (@lem175727 nat P Q). Qed.
Lemma lem175729 (m : nat) : (term278 m) = (term279 m).
Proof. exact (@lem175728 (term280 m) (term281 m)). Qed.
Lemma lem175730 (m : nat) (n : nat) : (term282 m n) = (term256 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem175731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175732 (m : nat) (n : nat) : (term283 m n) = (term257 m n).
Proof. exact (MK_COMB (@lem175731) (@lem175730 m n)). Qed.
Lemma lem175733 (m : nat) (n : nat) : (term284 m n) = (term274 m n).
Proof. exact (eq_refl (term284 m n)). Qed.
Lemma lem175734 (m : nat) (n : nat) : (term285 m n) = (term275 m n).
Proof. exact (MK_COMB (@lem175732 m n) (@lem175733 m n)). Qed.
Lemma lem175735 (m : nat) : (term286 m) = (term276 m).
Proof. exact (fun_ext (fun n : nat => @lem175734 m n)). Qed.
Lemma lem175736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175737 (m : nat) : (term278 m) = (term277 m).
Proof. exact (MK_COMB (@lem175736) (@lem175735 m)). Qed.
Lemma lem175738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem175739 (m : nat) : (term287 m) = (term288 m).
Proof. exact (MK_COMB (@lem175738) (@lem175737 m)). Qed.
Lemma lem175740 (m : nat) (n : nat) : (term282 m n) = (term256 m n).
Proof. exact (eq_refl (term282 m n)). Qed.
Lemma lem175741 (m : nat) : (term289 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem175740 m n)). Qed.
Lemma lem175742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175743 (m : nat) : (term290 m) = (term291 m).
Proof. exact (MK_COMB (@lem175742) (@lem175741 m)). Qed.
Lemma lem175744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175745 (m : nat) : (term292 m) = (term293 m).
Proof. exact (MK_COMB (@lem175744) (@lem175743 m)). Qed.
Lemma lem175746 (m : nat) (n : nat) : (term284 m n) = (term274 m n).
Proof. exact (eq_refl (term284 m n)). Qed.
Lemma lem175747 (m : nat) : (term294 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem175746 m n)). Qed.
Lemma lem175748 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175749 (m : nat) : (term295 m) = (term296 m).
Proof. exact (MK_COMB (@lem175748) (@lem175747 m)). Qed.
Lemma lem175750 (m : nat) : (term279 m) = (term297 m).
Proof. exact (MK_COMB (@lem175745 m) (@lem175749 m)). Qed.
Lemma lem175751 (m : nat) : ((term278 m) = (term279 m)) = ((term277 m) = (term297 m)).
Proof. exact (MK_COMB (@lem175739 m) (@lem175750 m)). Qed.
Lemma lem175752 (m : nat) : (term277 m) = (term297 m).
Proof. exact (EQ_MP (@lem175751 m) (@lem175729 m)). Qed.
Lemma lem175857 (m : nat) : (term207 m) = (term297 m).
Proof. exact (TRANS (@lem175725 m) (@lem175752 m)). Qed.
Lemma lem175858 : term208 = term298.
Proof. exact (fun_ext (fun m : nat => @lem175857 m)). Qed.
Lemma lem175859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175860 : term209 = term299.
Proof. exact (MK_COMB (@lem175859) (@lem175858)). Qed.
Lemma lem175862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem175863 (P : nat -> Prop) (Q : nat -> Prop) : (term212 P Q) = (term213 P Q).
Proof. exact (@lem175862 nat P Q). Qed.
Lemma lem175864 : term300 = term301.
Proof. exact (@lem175863 term302 term303). Qed.
Lemma lem175865 (m : nat) : (term304 m) = (term291 m).
Proof. exact (eq_refl (term304 m)). Qed.
Lemma lem175866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175867 (m : nat) : (term305 m) = (term293 m).
Proof. exact (MK_COMB (@lem175866) (@lem175865 m)). Qed.
Lemma lem175868 (m : nat) : (term306 m) = (term296 m).
Proof. exact (eq_refl (term306 m)). Qed.
Lemma lem175869 (m : nat) : (term307 m) = (term297 m).
Proof. exact (MK_COMB (@lem175867 m) (@lem175868 m)). Qed.
Lemma lem175870 : term308 = term298.
Proof. exact (fun_ext (fun m : nat => @lem175869 m)). Qed.
Lemma lem175871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175872 : term300 = term299.
Proof. exact (MK_COMB (@lem175871) (@lem175870)). Qed.
Lemma lem175873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem175874 : term309 = term310.
Proof. exact (MK_COMB (@lem175873) (@lem175872)). Qed.
Lemma lem175875 (m : nat) : (term304 m) = (term291 m).
Proof. exact (eq_refl (term304 m)). Qed.
Lemma lem175876 : term311 = term302.
Proof. exact (fun_ext (fun m : nat => @lem175875 m)). Qed.
Lemma lem175877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175878 : term312 = term313.
Proof. exact (MK_COMB (@lem175877) (@lem175876)). Qed.
Lemma lem175879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem175880 : term314 = term315.
Proof. exact (MK_COMB (@lem175879) (@lem175878)). Qed.
Lemma lem175881 (m : nat) : (term306 m) = (term296 m).
Proof. exact (eq_refl (term306 m)). Qed.
Lemma lem175882 : term316 = term303.
Proof. exact (fun_ext (fun m : nat => @lem175881 m)). Qed.
Lemma lem175883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem175884 : term317 = term318.
Proof. exact (MK_COMB (@lem175883) (@lem175882)). Qed.
Lemma lem175885 : term301 = term319.
Proof. exact (MK_COMB (@lem175880) (@lem175884)). Qed.
Lemma lem175886 : (term300 = term301) = (term299 = term319).
Proof. exact (MK_COMB (@lem175874) (@lem175885)). Qed.
Lemma lem175887 : term299 = term319.
Proof. exact (EQ_MP (@lem175886) (@lem175864)). Qed.
Lemma lem176002 : term209 = term319.
Proof. exact (TRANS (@lem175860) (@lem175887)). Qed.
Lemma lem176003 : term161 = term319.
Proof. exact (TRANS (@lem175587) (@lem176002)). Qed.
Lemma lem176004 (h1 : term161) : term319.
Proof. exact (EQ_MP (@lem176003) (@lem175372 h1)). Qed.
Lemma lem176020 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem176026 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem176038 (n : nat) (p : nat) (h1 : term154 n p) : term154 n p.
Proof. exact (h1). Qed.
Lemma lem176103 (n : nat) : ((term191 n) = (Nat.add n n)) = ((term191 n) = (Nat.add n n)).
Proof. exact (eq_refl ((term191 n) = (Nat.add n n))). Qed.
Lemma lem176104 : term192 = term192.
Proof. exact (fun_ext (fun n : nat => @lem176103 n)). Qed.
Lemma lem176105 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176106 : term193 = term193.
Proof. exact (MK_COMB (@lem176105) (@lem176104)). Qed.
Lemma lem176107 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem176106) (@lem175493 h1)). Qed.
Lemma lem176130 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem176131 (m : nat) : (term99 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem176130 n m)). Qed.
Lemma lem176132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176133 (m : nat) : (term100 m) = (term100 m).
Proof. exact (MK_COMB (@lem176132) (@lem176131 m)). Qed.
Lemma lem176134 : term101 = term101.
Proof. exact (fun_ext (fun m : nat => @lem176133 m)). Qed.
Lemma lem176135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176136 : term102 = term102.
Proof. exact (MK_COMB (@lem176135) (@lem176134)). Qed.
Lemma lem176137 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem176136) (@lem175563 h1)). Qed.
Lemma lem176142 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem176157 (m : nat) (n : nat) (p : nat) : (term262 m n p) = (term262 m n p).
Proof. exact (eq_refl (term262 m n p)). Qed.
Lemma lem176158 (m : nat) (n : nat) : (term260 m n) = (term260 m n).
Proof. exact (fun_ext (fun p : nat => @lem176157 m n p)). Qed.
Lemma lem176159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176160 (m : nat) (n : nat) : (term271 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem176159) (@lem176158 m n)). Qed.
Lemma lem176161 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem176162 (m : nat) (n : nat) : (term273 m n) = (term273 m n).
Proof. exact (MK_COMB (@lem176161) (@lem176160 m n)). Qed.
Lemma lem176163 (m : nat) (n : nat) : (term274 m n) = (term274 m n).
Proof. exact (MK_COMB (@lem176162 m n) (@lem176142 m n)). Qed.
Lemma lem176164 (m : nat) : (term281 m) = (term281 m).
Proof. exact (fun_ext (fun n : nat => @lem176163 m n)). Qed.
Lemma lem176165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176166 (m : nat) : (term296 m) = (term296 m).
Proof. exact (MK_COMB (@lem176165) (@lem176164 m)). Qed.
Lemma lem176167 : term303 = term303.
Proof. exact (fun_ext (fun m : nat => @lem176166 m)). Qed.
Lemma lem176168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176169 : term318 = term318.
Proof. exact (MK_COMB (@lem176168) (@lem176167)). Qed.
Lemma lem176176 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem176189 (m : nat) (n : nat) (p : nat) : (term185 m n p) = (term185 m n p).
Proof. exact (eq_refl (term185 m n p)). Qed.
Lemma lem176190 (m : nat) (n : nat) : (term243 m n) = (term243 m n).
Proof. exact (fun_ext (fun p : nat => @lem176189 m n p)). Qed.
Lemma lem176191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176192 (m : nat) (n : nat) : (term253 m n) = (term253 m n).
Proof. exact (MK_COMB (@lem176191) (@lem176190 m n)). Qed.
Lemma lem176193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem176194 (m : nat) (n : nat) : (term255 m n) = (term255 m n).
Proof. exact (MK_COMB (@lem176193) (@lem176192 m n)). Qed.
Lemma lem176195 (m : nat) (n : nat) : (term256 m n) = (term256 m n).
Proof. exact (MK_COMB (@lem176194 m n) (@lem176176 m n)). Qed.
Lemma lem176196 (m : nat) : (term280 m) = (term280 m).
Proof. exact (fun_ext (fun n : nat => @lem176195 m n)). Qed.
Lemma lem176197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176198 (m : nat) : (term291 m) = (term291 m).
Proof. exact (MK_COMB (@lem176197) (@lem176196 m)). Qed.
Lemma lem176199 : term302 = term302.
Proof. exact (fun_ext (fun m : nat => @lem176198 m)). Qed.
Lemma lem176200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176201 : term313 = term313.
Proof. exact (MK_COMB (@lem176200) (@lem176199)). Qed.
Lemma lem176202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem176203 : term315 = term315.
Proof. exact (MK_COMB (@lem176202) (@lem176201)). Qed.
Lemma lem176204 : term319 = term319.
Proof. exact (MK_COMB (@lem176203) (@lem176169)). Qed.
Lemma lem176205 (h1 : term161) : term319.
Proof. exact (EQ_MP (@lem176204) (@lem176004 h1)). Qed.
Lemma lem176206 (h1 : term161) : term318.
Proof. exact (proj2 (@lem176205 h1)). Qed.
Lemma lem176211 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem176215 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem176219 (n : nat) (p : nat) (h1 : term154 n p) : term154 n p.
Proof. exact (h1). Qed.
Lemma lem176249 (n : nat) : ((term191 n) = (Nat.add n n)) = ((term191 n) = (Nat.add n n)).
Proof. exact (eq_refl ((term191 n) = (Nat.add n n))). Qed.
Lemma lem176250 : term192 = term192.
Proof. exact (fun_ext (fun n : nat => @lem176249 n)). Qed.
Lemma lem176251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176253 : term193 = term193.
Proof. exact (MK_COMB (@lem176251) (@lem176250)). Qed.
Lemma lem176254 (h1 : term193) : term193.
Proof. exact (EQ_MP (@lem176253) (@lem176107 h1)). Qed.
Lemma lem176262 (n : nat) (m : nat) : (term97 n m) = (term97 n m).
Proof. exact (eq_refl (term97 n m)). Qed.
Lemma lem176263 (m : nat) : (term99 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem176262 n m)). Qed.
Lemma lem176264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176265 (m : nat) : (term100 m) = (term100 m).
Proof. exact (MK_COMB (@lem176264) (@lem176263 m)). Qed.
Lemma lem176266 : term101 = term101.
Proof. exact (fun_ext (fun m : nat => @lem176265 m)). Qed.
Lemma lem176267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176269 : term102 = term102.
Proof. exact (MK_COMB (@lem176267) (@lem176266)). Qed.
Lemma lem176270 (h1 : term69) : term102.
Proof. exact (EQ_MP (@lem176269) (@lem176137 h1)). Qed.
Lemma lem176320 {A : Type'} (P : A -> Prop) (Q : Prop) : (term238 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem176321 (P : nat -> Prop) (Q : Prop) : (term240 P Q) = (term239 P Q).
Proof. exact (@lem176320 nat P Q). Qed.
Lemma lem176322 (m : nat) (n : nat) : (term259 m n) = (term258 m n).
Proof. exact (@lem176321 (term260 m n) (Peano.lt m n)). Qed.
Lemma lem176323 (m : nat) (n : nat) (p : nat) : (term261 m n p) = (term262 m n p).
Proof. exact (eq_refl (term261 m n p)). Qed.
Lemma lem176324 (m : nat) (n : nat) : (term269 m n) = (term260 m n).
Proof. exact (fun_ext (fun p : nat => @lem176323 m n p)). Qed.
Lemma lem176325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176326 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem176325) (@lem176324 m n)). Qed.
Lemma lem176327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem176328 (m : nat) (n : nat) : (term272 m n) = (term273 m n).
Proof. exact (MK_COMB (@lem176327) (@lem176326 m n)). Qed.
Lemma lem176329 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem176330 (m : nat) (n : nat) : (term259 m n) = (term274 m n).
Proof. exact (MK_COMB (@lem176328 m n) (@lem176329 m n)). Qed.
Lemma lem176331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem176332 (m : nat) (n : nat) : (term320 m n) = (term321 m n).
Proof. exact (MK_COMB (@lem176331) (@lem176330 m n)). Qed.
Lemma lem176333 (m : nat) (n : nat) (p : nat) : (term261 m n p) = (term262 m n p).
Proof. exact (eq_refl (term261 m n p)). Qed.
Lemma lem176334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem176335 (m : nat) (n : nat) (p : nat) : (term263 m n p) = (term264 m n p).
Proof. exact (MK_COMB (@lem176334) (@lem176333 m n p)). Qed.
Lemma lem176336 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem176337 (p : nat) (m : nat) (n : nat) : (term265 p m n) = (term223 p m n).
Proof. exact (MK_COMB (@lem176335 m n p) (@lem176336 m n)). Qed.
Lemma lem176338 (m : nat) (n : nat) : (term266 m n) = (term217 m n).
Proof. exact (fun_ext (fun p : nat => @lem176337 p m n)). Qed.
Lemma lem176339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176340 (m : nat) (n : nat) : (term258 m n) = (term235 m n).
Proof. exact (MK_COMB (@lem176339) (@lem176338 m n)). Qed.
Lemma lem176341 (m : nat) (n : nat) : ((term259 m n) = (term258 m n)) = ((term274 m n) = (term235 m n)).
Proof. exact (MK_COMB (@lem176332 m n) (@lem176340 m n)). Qed.
Lemma lem176342 (m : nat) (n : nat) : (term274 m n) = (term235 m n).
Proof. exact (EQ_MP (@lem176341 m n) (@lem176322 m n)). Qed.
Lemma lem176343 (m : nat) : (term281 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem176342 m n)). Qed.
Lemma lem176344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176345 (m : nat) : (term296 m) = (term323 m).
Proof. exact (MK_COMB (@lem176344) (@lem176343 m)). Qed.
Lemma lem176346 : term303 = term324.
Proof. exact (fun_ext (fun m : nat => @lem176345 m)). Qed.
Lemma lem176347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176348 : term318 = term325.
Proof. exact (MK_COMB (@lem176347) (@lem176346)). Qed.
Lemma lem176355 (p : nat) (m : nat) (n : nat) : (term223 p m n) = (term223 p m n).
Proof. exact (eq_refl (term223 p m n)). Qed.
Lemma lem176356 (m : nat) (n : nat) : (term217 m n) = (term217 m n).
Proof. exact (fun_ext (fun p : nat => @lem176355 p m n)). Qed.
Lemma lem176357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176358 (m : nat) (n : nat) : (term235 m n) = (term235 m n).
Proof. exact (MK_COMB (@lem176357) (@lem176356 m n)). Qed.
Lemma lem176359 (m : nat) : (term322 m) = (term322 m).
Proof. exact (fun_ext (fun n : nat => @lem176358 m n)). Qed.
Lemma lem176360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176361 (m : nat) : (term323 m) = (term323 m).
Proof. exact (MK_COMB (@lem176360) (@lem176359 m)). Qed.
Lemma lem176362 : term324 = term324.
Proof. exact (fun_ext (fun m : nat => @lem176361 m)). Qed.
Lemma lem176363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem176364 : term325 = term325.
Proof. exact (MK_COMB (@lem176363) (@lem176362)). Qed.
Lemma lem176365 : term318 = term325.
Proof. exact (TRANS (@lem176348) (@lem176364)). Qed.
Lemma lem176366 (h1 : term161) : term325.
Proof. exact (EQ_MP (@lem176365) (@lem176206 h1)). Qed.
Lemma lem176379 (_3685 : nat) (h1 : term193) : term326 _3685.
Proof. exact (@lem176254 h1 _3685). Qed.
Lemma lem176380 (_3685 : nat) : (term326 _3685) = ((term191 _3685) = (Nat.add _3685 _3685)).
Proof. exact (eq_refl (term326 _3685)). Qed.
Lemma lem176382 (_3686 : nat) (h1 : term69) : term105 _3686.
Proof. exact (@lem176270 h1 _3686). Qed.
Lemma lem176383 (_3686 : nat) : (term105 _3686) = (term100 _3686).
Proof. exact (eq_refl (term105 _3686)). Qed.
Lemma lem176384 (_3686 : nat) (h1 : term69) : term100 _3686.
Proof. exact (EQ_MP (@lem176383 _3686) (@lem176382 _3686 h1)). Qed.
Lemma lem176385 (_3686 : nat) (_3687 : nat) (h1 : term69) : term106 _3686 _3687.
Proof. exact (@lem176384 _3686 h1 _3687). Qed.
Lemma lem176386 (_3687 : nat) (_3686 : nat) : (term106 _3686 _3687) = (term97 _3687 _3686).
Proof. exact (eq_refl (term106 _3686 _3687)). Qed.
Lemma lem176397 (_3691 : nat) (h1 : term161) : term327 _3691.
Proof. exact (@lem176366 h1 _3691). Qed.
Lemma lem176398 (_3691 : nat) : (term327 _3691) = (term323 _3691).
Proof. exact (eq_refl (term327 _3691)). Qed.
Lemma lem176399 (_3691 : nat) (h1 : term161) : term323 _3691.
Proof. exact (EQ_MP (@lem176398 _3691) (@lem176397 _3691 h1)). Qed.
Lemma lem176400 (_3691 : nat) (_3692 : nat) (h1 : term161) : term328 _3691 _3692.
Proof. exact (@lem176399 _3691 h1 _3692). Qed.
Lemma lem176401 (_3691 : nat) (_3692 : nat) : (term328 _3691 _3692) = (term235 _3691 _3692).
Proof. exact (eq_refl (term328 _3691 _3692)). Qed.
Lemma lem176402 (_3691 : nat) (_3692 : nat) (h1 : term161) : term235 _3691 _3692.
Proof. exact (EQ_MP (@lem176401 _3691 _3692) (@lem176400 _3691 _3692 h1)). Qed.
Lemma lem176403 (_3691 : nat) (_3692 : nat) (_3693 : nat) (h1 : term161) : term222 _3691 _3692 _3693.
Proof. exact (@lem176402 _3691 _3692 h1 _3693). Qed.
Lemma lem176404 (_3693 : nat) (_3691 : nat) (_3692 : nat) : (term222 _3691 _3692 _3693) = (term223 _3693 _3691 _3692).
Proof. exact (eq_refl (term222 _3691 _3692 _3693)). Qed.
Lemma lem176407 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem176409 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem176411 (n : nat) (p : nat) (h1 : term154 n p) : term154 n p.
Proof. exact (h1). Qed.
Lemma lem176431 (_3687 : nat) (_3686 : nat) (h1 : term69) : term97 _3687 _3686.
Proof. exact (EQ_MP (@lem176386 _3687 _3686) (@lem176385 _3686 _3687 h1)). Qed.
Lemma lem176443 (_3693 : nat) (_3691 : nat) (_3692 : nat) (h1 : term161) : term223 _3693 _3691 _3692.
Proof. exact (EQ_MP (@lem176404 _3693 _3691 _3692) (@lem176403 _3691 _3692 _3693 h1)). Qed.
Lemma lem176463 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem176464 (_3698 : nat) (_3700 : nat) (h1 : _3698 = _3700) : _3698 = _3700.
Proof. exact (h1). Qed.
Lemma lem176465 (_3699 : nat) (_3701 : nat) (h1 : _3699 = _3701) : _3699 = _3701.
Proof. exact (h1). Qed.
Lemma lem176466 (_3698 : nat) (_3700 : nat) (h1 : _3698 = _3700) : (Peano.lt _3698) = (Peano.lt _3700).
Proof. exact (MK_COMB (@lem176463) (@lem176464 _3698 _3700 h1)). Qed.
Lemma lem176467 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) (h1 : _3698 = _3700) (h2 : _3699 = _3701) : (Peano.lt _3698 _3699) = (Peano.lt _3700 _3701).
Proof. exact (MK_COMB (@lem176466 _3698 _3700 h1) (@lem176465 _3699 _3701 h2)). Qed.
Lemma lem176469 (b : Prop) (a : Prop) : term329 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem176470 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : term330 _3700 _3701 _3698 _3699.
Proof. exact (@lem176469 (Peano.lt _3700 _3701) (Peano.lt _3698 _3699)). Qed.
Lemma lem176471 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) (h1 : _3698 = _3700) (h2 : _3699 = _3701) : term331 _3700 _3701 _3698 _3699.
Proof. exact (@lem176470 _3700 _3701 _3698 _3699 (@lem176467 _3698 _3700 _3699 _3701 h1 h2)). Qed.
Lemma lem176472 (_3701 : nat) (_3699 : nat) (_3698 : nat) (_3700 : nat) (h1 : _3698 = _3700) : term332 _3700 _3701 _3698 _3699.
Proof. exact (fun h0 : _3699 = _3701 => @lem176471 _3698 _3700 _3699 _3701 h1 h0). Qed.
Lemma lem176474 (a : Prop) (b : Prop) : (a -> b) = (term333 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem176475 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term332 _3700 _3701 _3698 _3699) = (term334 _3700 _3701 _3698 _3699).
Proof. exact (@lem176474 (_3699 = _3701) (term331 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176476 (_3701 : nat) (_3699 : nat) (_3698 : nat) (_3700 : nat) (h1 : _3698 = _3700) : term334 _3700 _3701 _3698 _3699.
Proof. exact (EQ_MP (@lem176475 _3700 _3701 _3698 _3699) (@lem176472 _3701 _3699 _3698 _3700 h1)). Qed.
Lemma lem176477 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : term335 _3700 _3701 _3698 _3699.
Proof. exact (fun h0 : _3698 = _3700 => @lem176476 _3701 _3699 _3698 _3700 h0). Qed.
Lemma lem176479 (a : Prop) (b : Prop) : (a -> b) = (term333 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem176480 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term335 _3700 _3701 _3698 _3699) = (term336 _3700 _3701 _3698 _3699).
Proof. exact (@lem176479 (_3698 = _3700) (term334 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176481 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : term336 _3700 _3701 _3698 _3699.
Proof. exact (EQ_MP (@lem176480 _3700 _3701 _3698 _3699) (@lem176477 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176552 (x : nat) (y : nat) (z : nat) : term107 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem176554 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (h1). Qed.
Lemma lem176555 (p : nat) (n : nat) (h1 : Peano.le p n) : term108 p n.
Proof. exact (fun h0 : term109 p n => @lem176554 p n h1). Qed.
Lemma lem176557 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176558 (p : nat) (n : nat) : (term108 p n) = (Peano.le p n).
Proof. exact (@lem176557 (Peano.le p n)). Qed.
Lemma lem176559 (p : nat) (n : nat) (h1 : Peano.le p n) : Peano.le p n.
Proof. exact (EQ_MP (@lem176558 p n) (@lem176555 p n h1)). Qed.
Lemma lem176565 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem176566 (_3687 : nat) (_3686 : nat) : (term97 _3687 _3686) = (term111 _3687 _3686).
Proof. exact (@lem176565 ((term98 _3686 _3687) = _3686) (term109 _3687 _3686)). Qed.
Lemma lem176574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem176575 (_3687 : nat) (_3686 : nat) : (term112 _3687 _3686) = (term113 _3687 _3686).
Proof. exact (MK_COMB (@lem176574) (@lem176566 _3687 _3686)). Qed.
Lemma lem176583 (_3687 : nat) (_3686 : nat) : (term111 _3687 _3686) = (term111 _3687 _3686).
Proof. exact (eq_refl (term111 _3687 _3686)). Qed.
Lemma lem176584 (_3687 : nat) (_3686 : nat) : ((term97 _3687 _3686) = (term111 _3687 _3686)) = ((term111 _3687 _3686) = (term111 _3687 _3686)).
Proof. exact (MK_COMB (@lem176575 _3687 _3686) (@lem176583 _3687 _3686)). Qed.
Lemma lem176586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem176587 (x : Prop) : (x = x) = True.
Proof. exact (@lem176586 Prop x). Qed.
Lemma lem176588 (_3687 : nat) (_3686 : nat) : ((term111 _3687 _3686) = (term111 _3687 _3686)) = True.
Proof. exact (@lem176587 (term111 _3687 _3686)). Qed.
Lemma lem176589 (_3687 : nat) (_3686 : nat) : ((term97 _3687 _3686) = (term111 _3687 _3686)) = True.
Proof. exact (TRANS (@lem176584 _3687 _3686) (@lem176588 _3687 _3686)). Qed.
Lemma lem176590 (_3687 : nat) (_3686 : nat) : True = ((term97 _3687 _3686) = (term111 _3687 _3686)).
Proof. exact (SYM (@lem176589 _3687 _3686)). Qed.
Lemma lem176591 (_3687 : nat) (_3686 : nat) : (term97 _3687 _3686) = (term111 _3687 _3686).
Proof. exact (EQ_MP (@lem176590 _3687 _3686) (@lem0)). Qed.
Lemma lem176592 (_3687 : nat) (_3686 : nat) (h1 : term69) : term111 _3687 _3686.
Proof. exact (EQ_MP (@lem176591 _3687 _3686) (@lem176431 _3687 _3686 h1)). Qed.
Lemma lem176594 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem176595 (_3687 : nat) (_3686 : nat) : (term111 _3687 _3686) = (term115 _3687 _3686).
Proof. exact (@lem176594 (term109 _3687 _3686) ((term98 _3686 _3687) = _3686)). Qed.
Lemma lem176597 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176598 (_3687 : nat) (_3686 : nat) : (term117 _3687 _3686) = (Peano.le _3687 _3686).
Proof. exact (@lem176597 (Peano.le _3687 _3686)). Qed.
Lemma lem176599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem176600 (_3687 : nat) (_3686 : nat) : (term118 _3687 _3686) = (term76 _3687 _3686).
Proof. exact (MK_COMB (@lem176599) (@lem176598 _3687 _3686)). Qed.
Lemma lem176601 (_3687 : nat) (_3686 : nat) : ((term98 _3686 _3687) = _3686) = ((term98 _3686 _3687) = _3686).
Proof. exact (eq_refl ((term98 _3686 _3687) = _3686)). Qed.
Lemma lem176602 (_3687 : nat) (_3686 : nat) : (term115 _3687 _3686) = (term89 _3687 _3686).
Proof. exact (MK_COMB (@lem176600 _3687 _3686) (@lem176601 _3687 _3686)). Qed.
Lemma lem176603 (_3687 : nat) (_3686 : nat) : (term111 _3687 _3686) = (term89 _3687 _3686).
Proof. exact (TRANS (@lem176595 _3687 _3686) (@lem176602 _3687 _3686)). Qed.
Lemma lem176606 (_3687 : nat) (_3686 : nat) (h1 : term69) : term89 _3687 _3686.
Proof. exact (EQ_MP (@lem176603 _3687 _3686) (@lem176592 _3687 _3686 h1)). Qed.
Lemma lem176607 (p : nat) (n : nat) (h1 : term69) : term89 p n.
Proof. exact (@lem176606 p n h1). Qed.
Lemma lem176610 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : (term98 n p) = n.
Proof. exact (@lem176607 p n h1 (@lem176559 p n h2)). Qed.
Lemma lem176611 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : term119 p n.
Proof. exact (fun h0 : term120 p n => @lem176610 p n h1 h2). Qed.
Lemma lem176613 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176614 (p : nat) (n : nat) : (term119 p n) = ((term98 n p) = n).
Proof. exact (@lem176613 ((term98 n p) = n)). Qed.
Lemma lem176615 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : (term98 n p) = n.
Proof. exact (EQ_MP (@lem176614 p n) (@lem176611 p n h1 h2)). Qed.
Lemma lem176617 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem176618 (n : nat) (p : nat) : (term98 n p) = (term98 n p).
Proof. exact (@lem176617 (term98 n p)). Qed.
Lemma lem176619 (n : nat) (p : nat) : term337 n p.
Proof. exact (fun h0 : term338 n p => @lem176618 n p). Qed.
Lemma lem176621 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176622 (n : nat) (p : nat) : (term337 n p) = ((term98 n p) = (term98 n p)).
Proof. exact (@lem176621 ((term98 n p) = (term98 n p))). Qed.
Lemma lem176623 (n : nat) (p : nat) : (term98 n p) = (term98 n p).
Proof. exact (EQ_MP (@lem176622 n p) (@lem176619 n p)). Qed.
Lemma lem176641 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem176642 (y : nat) (x : nat) (z : nat) : (term123 x y z) = (term124 y x z).
Proof. exact (@lem176641 (y = z) (term125 x z)). Qed.
Lemma lem176652 (x : nat) (y : nat) : (term126 x y) = (term126 x y).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem176653 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term127 y x z).
Proof. exact (MK_COMB (@lem176652 x y) (@lem176642 y x z)). Qed.
Lemma lem176657 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem176658 (y : nat) (x : nat) (z : nat) : (term127 y x z) = (term129 y x z).
Proof. exact (@lem176657 (y = z) (term125 x y) (term125 x z)). Qed.
Lemma lem176680 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term129 y x z).
Proof. exact (TRANS (@lem176653 y x z) (@lem176658 y x z)). Qed.
Lemma lem176681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem176682 (y : nat) (x : nat) (z : nat) : (term130 x y z) = (term131 y x z).
Proof. exact (MK_COMB (@lem176681) (@lem176680 y x z)). Qed.
Lemma lem176704 (y : nat) (x : nat) (z : nat) : (term129 y x z) = (term129 y x z).
Proof. exact (eq_refl (term129 y x z)). Qed.
Lemma lem176705 (y : nat) (x : nat) (z : nat) : ((term107 x y z) = (term129 y x z)) = ((term129 y x z) = (term129 y x z)).
Proof. exact (MK_COMB (@lem176682 y x z) (@lem176704 y x z)). Qed.
Lemma lem176707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem176708 (x : Prop) : (x = x) = True.
Proof. exact (@lem176707 Prop x). Qed.
Lemma lem176709 (y : nat) (x : nat) (z : nat) : ((term129 y x z) = (term129 y x z)) = True.
Proof. exact (@lem176708 (term129 y x z)). Qed.
Lemma lem176710 (y : nat) (x : nat) (z : nat) : ((term107 x y z) = (term129 y x z)) = True.
Proof. exact (TRANS (@lem176705 y x z) (@lem176709 y x z)). Qed.
Lemma lem176711 (y : nat) (x : nat) (z : nat) : True = ((term107 x y z) = (term129 y x z)).
Proof. exact (SYM (@lem176710 y x z)). Qed.
Lemma lem176712 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term129 y x z).
Proof. exact (EQ_MP (@lem176711 y x z) (@lem0)). Qed.
Lemma lem176713 (y : nat) (x : nat) (z : nat) : term129 y x z.
Proof. exact (EQ_MP (@lem176712 y x z) (@lem176552 x y z)). Qed.
Lemma lem176715 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem176716 (x : nat) (y : nat) (z : nat) : (term129 y x z) = (term132 x y z).
Proof. exact (@lem176715 (term133 y x z) (y = z)). Qed.
Lemma lem176718 (a : Prop) (b : Prop) : (term134 a b) = (term135 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem176719 (y : nat) (x : nat) (z : nat) : (term136 y x z) = (term137 y x z).
Proof. exact (@lem176718 (term125 x y) (term125 x z)). Qed.
Lemma lem176721 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176722 (x : nat) (y : nat) : (term138 x y) = (x = y).
Proof. exact (@lem176721 (x = y)). Qed.
Lemma lem176723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem176724 (x : nat) (y : nat) : (term139 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem176723) (@lem176722 x y)). Qed.
Lemma lem176726 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176727 (x : nat) (z : nat) : (term138 x z) = (x = z).
Proof. exact (@lem176726 (x = z)). Qed.
Lemma lem176728 (y : nat) (x : nat) (z : nat) : (term137 y x z) = (term141 y x z).
Proof. exact (MK_COMB (@lem176724 x y) (@lem176727 x z)). Qed.
Lemma lem176729 (y : nat) (x : nat) (z : nat) : (term136 y x z) = (term141 y x z).
Proof. exact (TRANS (@lem176719 y x z) (@lem176728 y x z)). Qed.
Lemma lem176730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem176731 (y : nat) (x : nat) (z : nat) : (term142 y x z) = (term143 y x z).
Proof. exact (MK_COMB (@lem176730) (@lem176729 y x z)). Qed.
Lemma lem176732 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem176733 (x : nat) (y : nat) (z : nat) : (term132 x y z) = (term144 x y z).
Proof. exact (MK_COMB (@lem176731 y x z) (@lem176732 y z)). Qed.
Lemma lem176734 (x : nat) (y : nat) (z : nat) : (term129 y x z) = (term144 x y z).
Proof. exact (TRANS (@lem176716 x y z) (@lem176733 x y z)). Qed.
Lemma lem176736 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : term339 n p.
Proof. exact (conj (@lem176615 p n h1 h2) (@lem176623 n p)). Qed.
Lemma lem176738 (x : nat) (y : nat) (z : nat) : term144 x y z.
Proof. exact (EQ_MP (@lem176734 x y z) (@lem176713 y x z)). Qed.
Lemma lem176739 (n : nat) (p : nat) : term340 n p.
Proof. exact (@lem176738 (term98 n p) n (term98 n p)). Qed.
Lemma lem176742 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : n = (term98 n p).
Proof. exact (@lem176739 n p (@lem176736 p n h1 h2)). Qed.
Lemma lem176743 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : term341 n p.
Proof. exact (fun h0 : term342 n p => @lem176742 p n h1 h2). Qed.
Lemma lem176745 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176746 (n : nat) (p : nat) : (term341 n p) = (n = (term98 n p)).
Proof. exact (@lem176745 (n = (term98 n p))). Qed.
Lemma lem176747 (p : nat) (n : nat) (h1 : term69) (h2 : Peano.le p n) : n = (term98 n p).
Proof. exact (EQ_MP (@lem176746 n p) (@lem176743 p n h1 h2)). Qed.
Lemma lem176749 (_3685 : nat) (h1 : term193) : (term191 _3685) = (Nat.add _3685 _3685).
Proof. exact (EQ_MP (@lem176380 _3685) (@lem176379 _3685 h1)). Qed.
Lemma lem176750 (p : nat) (h1 : term193) : (term191 p) = (Nat.add p p).
Proof. exact (@lem176749 p h1). Qed.
Lemma lem176751 (p : nat) (h1 : term193) : term343 p.
Proof. exact (fun h0 : term344 p => @lem176750 p h1). Qed.
Lemma lem176753 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176754 (p : nat) : (term343 p) = ((term191 p) = (Nat.add p p)).
Proof. exact (@lem176753 ((term191 p) = (Nat.add p p))). Qed.
Lemma lem176755 (p : nat) (h1 : term193) : (term191 p) = (Nat.add p p).
Proof. exact (EQ_MP (@lem176754 p) (@lem176751 p h1)). Qed.
Lemma lem176757 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (h1). Qed.
Lemma lem176758 (n : nat) (p : nat) (h1 : term30 n p) : term345 n p.
Proof. exact (fun h0 : term346 n p => @lem176757 n p h1). Qed.
Lemma lem176760 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176761 (n : nat) (p : nat) : (term345 n p) = (term30 n p).
Proof. exact (@lem176760 (term30 n p)). Qed.
Lemma lem176762 (n : nat) (p : nat) (h1 : term30 n p) : term30 n p.
Proof. exact (EQ_MP (@lem176761 n p) (@lem176758 n p h1)). Qed.
Lemma lem176780 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem176781 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term334 _3700 _3701 _3698 _3699) = (term347 _3700 _3701 _3698 _3699).
Proof. exact (@lem176780 (Peano.lt _3700 _3701) (term125 _3699 _3701) (term8 _3698 _3699)). Qed.
Lemma lem176795 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem176796 (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term348 _3701 _3698 _3699) = (term349 _3698 _3699 _3701).
Proof. exact (@lem176795 (term8 _3698 _3699) (term125 _3699 _3701)). Qed.
Lemma lem176804 (_3700 : nat) (_3701 : nat) : (term350 _3700 _3701) = (term350 _3700 _3701).
Proof. exact (eq_refl (term350 _3700 _3701)). Qed.
Lemma lem176805 (_3700 : nat) (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term347 _3700 _3701 _3698 _3699) = (term351 _3700 _3698 _3699 _3701).
Proof. exact (MK_COMB (@lem176804 _3700 _3701) (@lem176796 _3698 _3699 _3701)). Qed.
Lemma lem176816 (_3700 : nat) (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term334 _3700 _3701 _3698 _3699) = (term351 _3700 _3698 _3699 _3701).
Proof. exact (TRANS (@lem176781 _3700 _3701 _3698 _3699) (@lem176805 _3700 _3698 _3699 _3701)). Qed.
Lemma lem176817 (_3698 : nat) (_3700 : nat) : (term126 _3698 _3700) = (term126 _3698 _3700).
Proof. exact (eq_refl (term126 _3698 _3700)). Qed.
Lemma lem176818 (_3700 : nat) (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term336 _3700 _3701 _3698 _3699) = (term352 _3700 _3698 _3699 _3701).
Proof. exact (MK_COMB (@lem176817 _3698 _3700) (@lem176816 _3700 _3698 _3699 _3701)). Qed.
Lemma lem176822 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem176823 (_3700 : nat) (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term352 _3700 _3698 _3699 _3701) = (term353 _3700 _3698 _3699 _3701).
Proof. exact (@lem176822 (Peano.lt _3700 _3701) (term125 _3698 _3700) (term349 _3698 _3699 _3701)). Qed.
Lemma lem176837 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem176838 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term354 _3700 _3698 _3699 _3701) = (term355 _3698 _3700 _3699 _3701).
Proof. exact (@lem176837 (term8 _3698 _3699) (term125 _3698 _3700) (term125 _3699 _3701)). Qed.
Lemma lem176858 (_3700 : nat) (_3701 : nat) : (term350 _3700 _3701) = (term350 _3700 _3701).
Proof. exact (eq_refl (term350 _3700 _3701)). Qed.
Lemma lem176859 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term353 _3700 _3698 _3699 _3701) = (term356 _3698 _3700 _3699 _3701).
Proof. exact (MK_COMB (@lem176858 _3700 _3701) (@lem176838 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176870 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term352 _3700 _3698 _3699 _3701) = (term356 _3698 _3700 _3699 _3701).
Proof. exact (TRANS (@lem176823 _3700 _3698 _3699 _3701) (@lem176859 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176871 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term336 _3700 _3701 _3698 _3699) = (term356 _3698 _3700 _3699 _3701).
Proof. exact (TRANS (@lem176818 _3700 _3698 _3699 _3701) (@lem176870 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176872 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem176873 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term357 _3700 _3701 _3698 _3699) = (term358 _3698 _3700 _3699 _3701).
Proof. exact (MK_COMB (@lem176872) (@lem176871 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176899 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem176900 (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term348 _3701 _3698 _3699) = (term349 _3698 _3699 _3701).
Proof. exact (@lem176899 (term8 _3698 _3699) (term125 _3699 _3701)). Qed.
Lemma lem176908 (_3698 : nat) (_3700 : nat) : (term126 _3698 _3700) = (term126 _3698 _3700).
Proof. exact (eq_refl (term126 _3698 _3700)). Qed.
Lemma lem176909 (_3700 : nat) (_3698 : nat) (_3699 : nat) (_3701 : nat) : (term359 _3700 _3701 _3698 _3699) = (term354 _3700 _3698 _3699 _3701).
Proof. exact (MK_COMB (@lem176908 _3698 _3700) (@lem176900 _3698 _3699 _3701)). Qed.
Lemma lem176913 (q : Prop) (p : Prop) (r : Prop) : (term128 p q r) = (term128 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem176914 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term354 _3700 _3698 _3699 _3701) = (term355 _3698 _3700 _3699 _3701).
Proof. exact (@lem176913 (term8 _3698 _3699) (term125 _3698 _3700) (term125 _3699 _3701)). Qed.
Lemma lem176934 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term359 _3700 _3701 _3698 _3699) = (term355 _3698 _3700 _3699 _3701).
Proof. exact (TRANS (@lem176909 _3700 _3698 _3699 _3701) (@lem176914 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176935 (_3700 : nat) (_3701 : nat) : (term350 _3700 _3701) = (term350 _3700 _3701).
Proof. exact (eq_refl (term350 _3700 _3701)). Qed.
Lemma lem176936 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : (term360 _3700 _3701 _3698 _3699) = (term356 _3698 _3700 _3699 _3701).
Proof. exact (MK_COMB (@lem176935 _3700 _3701) (@lem176934 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176947 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : ((term336 _3700 _3701 _3698 _3699) = (term360 _3700 _3701 _3698 _3699)) = ((term356 _3698 _3700 _3699 _3701) = (term356 _3698 _3700 _3699 _3701)).
Proof. exact (MK_COMB (@lem176873 _3698 _3700 _3699 _3701) (@lem176936 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176949 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem176950 (x : Prop) : (x = x) = True.
Proof. exact (@lem176949 Prop x). Qed.
Lemma lem176951 (_3698 : nat) (_3700 : nat) (_3699 : nat) (_3701 : nat) : ((term356 _3698 _3700 _3699 _3701) = (term356 _3698 _3700 _3699 _3701)) = True.
Proof. exact (@lem176950 (term356 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176952 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : ((term336 _3700 _3701 _3698 _3699) = (term360 _3700 _3701 _3698 _3699)) = True.
Proof. exact (TRANS (@lem176947 _3698 _3700 _3699 _3701) (@lem176951 _3698 _3700 _3699 _3701)). Qed.
Lemma lem176953 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : True = ((term336 _3700 _3701 _3698 _3699) = (term360 _3700 _3701 _3698 _3699)).
Proof. exact (SYM (@lem176952 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176954 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term336 _3700 _3701 _3698 _3699) = (term360 _3700 _3701 _3698 _3699).
Proof. exact (EQ_MP (@lem176953 _3700 _3701 _3698 _3699) (@lem0)). Qed.
Lemma lem176955 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : term360 _3700 _3701 _3698 _3699.
Proof. exact (EQ_MP (@lem176954 _3700 _3701 _3698 _3699) (@lem176481 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176957 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem176958 (_3698 : nat) (_3699 : nat) (_3700 : nat) (_3701 : nat) : (term360 _3700 _3701 _3698 _3699) = (term361 _3698 _3699 _3700 _3701).
Proof. exact (@lem176957 (term359 _3700 _3701 _3698 _3699) (Peano.lt _3700 _3701)). Qed.
Lemma lem176960 (a : Prop) (b : Prop) : (term134 a b) = (term135 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem176961 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term362 _3700 _3701 _3698 _3699) = (term363 _3700 _3701 _3698 _3699).
Proof. exact (@lem176960 (term125 _3698 _3700) (term348 _3701 _3698 _3699)). Qed.
Lemma lem176963 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176964 (_3698 : nat) (_3700 : nat) : (term138 _3698 _3700) = (_3698 = _3700).
Proof. exact (@lem176963 (_3698 = _3700)). Qed.
Lemma lem176965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem176966 (_3698 : nat) (_3700 : nat) : (term139 _3698 _3700) = (term140 _3698 _3700).
Proof. exact (MK_COMB (@lem176965) (@lem176964 _3698 _3700)). Qed.
Lemma lem176968 (a : Prop) (b : Prop) : (term134 a b) = (term135 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem176969 (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term364 _3701 _3698 _3699) = (term365 _3701 _3698 _3699).
Proof. exact (@lem176968 (term125 _3699 _3701) (term8 _3698 _3699)). Qed.
Lemma lem176971 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176972 (_3699 : nat) (_3701 : nat) : (term138 _3699 _3701) = (_3699 = _3701).
Proof. exact (@lem176971 (_3699 = _3701)). Qed.
Lemma lem176973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem176974 (_3699 : nat) (_3701 : nat) : (term139 _3699 _3701) = (term140 _3699 _3701).
Proof. exact (MK_COMB (@lem176973) (@lem176972 _3699 _3701)). Qed.
Lemma lem176976 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem176977 (_3698 : nat) (_3699 : nat) : (term366 _3698 _3699) = (Peano.lt _3698 _3699).
Proof. exact (@lem176976 (Peano.lt _3698 _3699)). Qed.
Lemma lem176978 (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term365 _3701 _3698 _3699) = (term367 _3701 _3698 _3699).
Proof. exact (MK_COMB (@lem176974 _3699 _3701) (@lem176977 _3698 _3699)). Qed.
Lemma lem176979 (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term364 _3701 _3698 _3699) = (term367 _3701 _3698 _3699).
Proof. exact (TRANS (@lem176969 _3701 _3698 _3699) (@lem176978 _3701 _3698 _3699)). Qed.
Lemma lem176980 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term363 _3700 _3701 _3698 _3699) = (term368 _3700 _3701 _3698 _3699).
Proof. exact (MK_COMB (@lem176966 _3698 _3700) (@lem176979 _3701 _3698 _3699)). Qed.
Lemma lem176981 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term362 _3700 _3701 _3698 _3699) = (term368 _3700 _3701 _3698 _3699).
Proof. exact (TRANS (@lem176961 _3700 _3701 _3698 _3699) (@lem176980 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem176983 (_3700 : nat) (_3701 : nat) (_3698 : nat) (_3699 : nat) : (term369 _3700 _3701 _3698 _3699) = (term370 _3700 _3701 _3698 _3699).
Proof. exact (MK_COMB (@lem176982) (@lem176981 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176984 (_3700 : nat) (_3701 : nat) : (Peano.lt _3700 _3701) = (Peano.lt _3700 _3701).
Proof. exact (eq_refl (Peano.lt _3700 _3701)). Qed.
Lemma lem176985 (_3698 : nat) (_3699 : nat) (_3700 : nat) (_3701 : nat) : (term361 _3698 _3699 _3700 _3701) = (term371 _3698 _3699 _3700 _3701).
Proof. exact (MK_COMB (@lem176983 _3700 _3701 _3698 _3699) (@lem176984 _3700 _3701)). Qed.
Lemma lem176986 (_3698 : nat) (_3699 : nat) (_3700 : nat) (_3701 : nat) : (term360 _3700 _3701 _3698 _3699) = (term371 _3698 _3699 _3700 _3701).
Proof. exact (TRANS (@lem176958 _3698 _3699 _3700 _3701) (@lem176985 _3698 _3699 _3700 _3701)). Qed.
Lemma lem176988 (n : nat) (p : nat) (h1 : term193) (h2 : term30 n p) : term372 n p.
Proof. exact (conj (@lem176755 p h1) (@lem176762 n p h2)). Qed.
Lemma lem176989 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term30 n p) (h4 : Peano.le p n) : term373 n p.
Proof. exact (conj (@lem176747 p n h1 h4) (@lem176988 n p h2 h3)). Qed.
Lemma lem176991 (_3698 : nat) (_3699 : nat) (_3700 : nat) (_3701 : nat) : term371 _3698 _3699 _3700 _3701.
Proof. exact (EQ_MP (@lem176986 _3698 _3699 _3700 _3701) (@lem176955 _3700 _3701 _3698 _3699)). Qed.
Lemma lem176992 (n : nat) (p : nat) : term374 n p.
Proof. exact (@lem176991 n (term191 p) (term98 n p) (Nat.add p p)). Qed.
Lemma lem176995 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term30 n p) (h4 : Peano.le p n) : term375 n p.
Proof. exact (@lem176992 n p (@lem176989 p n h1 h2 h3 h4)). Qed.
Lemma lem176996 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term30 n p) (h4 : Peano.le p n) : term376 n p.
Proof. exact (fun h0 : term377 n p => @lem176995 p n h1 h2 h3 h4). Qed.
Lemma lem176998 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem176999 (n : nat) (p : nat) : (term376 n p) = (term375 n p).
Proof. exact (@lem176998 (term375 n p)). Qed.
Lemma lem177000 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term30 n p) (h4 : Peano.le p n) : term375 n p.
Proof. exact (EQ_MP (@lem176999 n p) (@lem176996 p n h1 h2 h3 h4)). Qed.
Lemma lem177006 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem177007 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term223 _3693 _3691 _3692) = (term378 _3691 _3692 _3693).
Proof. exact (@lem177006 (Peano.lt _3691 _3692) (term262 _3691 _3692 _3693)). Qed.
Lemma lem177013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem177014 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term379 _3693 _3691 _3692) = (term380 _3691 _3692 _3693).
Proof. exact (MK_COMB (@lem177013) (@lem177007 _3691 _3692 _3693)). Qed.
Lemma lem177020 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term378 _3691 _3692 _3693) = (term378 _3691 _3692 _3693).
Proof. exact (eq_refl (term378 _3691 _3692 _3693)). Qed.
Lemma lem177021 (_3691 : nat) (_3692 : nat) (_3693 : nat) : ((term223 _3693 _3691 _3692) = (term378 _3691 _3692 _3693)) = ((term378 _3691 _3692 _3693) = (term378 _3691 _3692 _3693)).
Proof. exact (MK_COMB (@lem177014 _3691 _3692 _3693) (@lem177020 _3691 _3692 _3693)). Qed.
Lemma lem177023 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem177024 (x : Prop) : (x = x) = True.
Proof. exact (@lem177023 Prop x). Qed.
Lemma lem177025 (_3691 : nat) (_3692 : nat) (_3693 : nat) : ((term378 _3691 _3692 _3693) = (term378 _3691 _3692 _3693)) = True.
Proof. exact (@lem177024 (term378 _3691 _3692 _3693)). Qed.
Lemma lem177026 (_3691 : nat) (_3692 : nat) (_3693 : nat) : ((term223 _3693 _3691 _3692) = (term378 _3691 _3692 _3693)) = True.
Proof. exact (TRANS (@lem177021 _3691 _3692 _3693) (@lem177025 _3691 _3692 _3693)). Qed.
Lemma lem177027 (_3691 : nat) (_3692 : nat) (_3693 : nat) : True = ((term223 _3693 _3691 _3692) = (term378 _3691 _3692 _3693)).
Proof. exact (SYM (@lem177026 _3691 _3692 _3693)). Qed.
Lemma lem177028 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term223 _3693 _3691 _3692) = (term378 _3691 _3692 _3693).
Proof. exact (EQ_MP (@lem177027 _3691 _3692 _3693) (@lem0)). Qed.
Lemma lem177029 (_3691 : nat) (_3692 : nat) (_3693 : nat) (h1 : term161) : term378 _3691 _3692 _3693.
Proof. exact (EQ_MP (@lem177028 _3691 _3692 _3693) (@lem176443 _3693 _3691 _3692 h1)). Qed.
Lemma lem177031 (b : Prop) (a : Prop) : (a \/ b) = (term114 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem177032 (_3693 : nat) (_3691 : nat) (_3692 : nat) : (term378 _3691 _3692 _3693) = (term381 _3693 _3691 _3692).
Proof. exact (@lem177031 (term262 _3691 _3692 _3693) (Peano.lt _3691 _3692)). Qed.
Lemma lem177034 (a : Prop) : (term116 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem177035 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term382 _3691 _3692 _3693) = (term185 _3691 _3692 _3693).
Proof. exact (@lem177034 (term185 _3691 _3692 _3693)). Qed.
Lemma lem177036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem177037 (_3691 : nat) (_3692 : nat) (_3693 : nat) : (term383 _3691 _3692 _3693) = (term384 _3691 _3692 _3693).
Proof. exact (MK_COMB (@lem177036) (@lem177035 _3691 _3692 _3693)). Qed.
Lemma lem177038 (_3691 : nat) (_3692 : nat) : (Peano.lt _3691 _3692) = (Peano.lt _3691 _3692).
Proof. exact (eq_refl (Peano.lt _3691 _3692)). Qed.
Lemma lem177039 (_3693 : nat) (_3691 : nat) (_3692 : nat) : (term381 _3693 _3691 _3692) = (term385 _3693 _3691 _3692).
Proof. exact (MK_COMB (@lem177037 _3691 _3692 _3693) (@lem177038 _3691 _3692)). Qed.
Lemma lem177040 (_3693 : nat) (_3691 : nat) (_3692 : nat) : (term378 _3691 _3692 _3693) = (term385 _3693 _3691 _3692).
Proof. exact (TRANS (@lem177032 _3693 _3691 _3692) (@lem177039 _3693 _3691 _3692)). Qed.
Lemma lem177043 (_3693 : nat) (_3691 : nat) (_3692 : nat) (h1 : term161) : term385 _3693 _3691 _3692.
Proof. exact (EQ_MP (@lem177040 _3693 _3691 _3692) (@lem177029 _3691 _3692 _3693 h1)). Qed.
Lemma lem177044 (n : nat) (p : nat) (h1 : term161) : term386 n p.
Proof. exact (@lem177043 p (Nat.sub n p) p h1). Qed.
Lemma lem177047 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term30 n p) (h5 : Peano.le p n) : term152 n p.
Proof. exact (@lem177044 n p h1 (@lem177000 p n h2 h3 h4 h5)). Qed.
Lemma lem177048 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term30 n p) (h5 : Peano.le p n) : term387 n p.
Proof. exact (fun h0 : term154 n p => @lem177047 p n h1 h2 h3 h4 h5). Qed.
Lemma lem177050 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177051 (n : nat) (p : nat) : (term387 n p) = (term152 n p).
Proof. exact (@lem177050 (term152 n p)). Qed.
Lemma lem177052 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term30 n p) (h5 : Peano.le p n) : term152 n p.
Proof. exact (EQ_MP (@lem177051 n p) (@lem177048 p n h1 h2 h3 h4 h5)). Qed.
Lemma lem177055 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem177057 (n : nat) (p : nat) : (term154 n p) = (term388 n p).
Proof. exact (@lem177055 (term152 n p)). Qed.
Lemma lem177060 (n : nat) (p : nat) (h1 : term154 n p) : term388 n p.
Proof. exact (EQ_MP (@lem177057 n p) (@lem176411 n p h1)). Qed.
Lemma lem177063 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (@lem177060 n p h4 (@lem177052 p n h1 h2 h3 h5 h6)). Qed.
Lemma lem177064 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : term149.
Proof. exact (fun h0 : ~ False => @lem177063 p n h1 h2 h3 h4 h5 h6). Qed.
Lemma lem177066 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177067 : term149 = False.
Proof. exact (@lem177066 False). Qed.
Lemma lem177068 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177067) (@lem177064 p n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem177069 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term154 n p) = False.
Proof. exact (prop_ext (fun h7 : term154 n p => @lem177068 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176411 n p h4)). Qed.
Lemma lem177070 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177069 p n h1 h2 h3 h4 h5 h6) (@lem176411 n p h4)). Qed.
Lemma lem177071 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h7 : Peano.le p n => @lem177070 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176409 p n h6)). Qed.
Lemma lem177072 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177071 p n h1 h2 h3 h4 h5 h6) (@lem176409 p n h6)). Qed.
Lemma lem177073 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term30 n p) = False.
Proof. exact (prop_ext (fun h7 : term30 n p => @lem177072 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176407 n p h5)). Qed.
Lemma lem177074 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177073 p n h1 h2 h3 h4 h5 h6) (@lem176407 n p h5)). Qed.
Lemma lem177075 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term154 n p) = False.
Proof. exact (prop_ext (fun h7 : term154 n p => @lem177074 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176219 n p h4)). Qed.
Lemma lem177076 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177075 p n h1 h2 h3 h4 h5 h6) (@lem176219 n p h4)). Qed.
Lemma lem177077 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h7 : Peano.le p n => @lem177076 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176215 p n h6)). Qed.
Lemma lem177078 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177077 p n h1 h2 h3 h4 h5 h6) (@lem176215 p n h6)). Qed.
Lemma lem177079 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term30 n p) = False.
Proof. exact (prop_ext (fun h7 : term30 n p => @lem177078 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176211 n p h5)). Qed.
Lemma lem177080 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177079 p n h1 h2 h3 h4 h5 h6) (@lem176211 n p h5)). Qed.
Lemma lem177081 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : term193 = False.
Proof. exact (prop_ext (fun h7 : term193 => @lem177080 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176254 h3)). Qed.
Lemma lem177082 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177081 p n h1 h2 h3 h4 h5 h6) (@lem176254 h3)). Qed.
Lemma lem177083 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term154 n p) = False.
Proof. exact (prop_ext (fun h7 : term154 n p => @lem177082 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176219 n p h4)). Qed.
Lemma lem177084 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177083 p n h1 h2 h3 h4 h5 h6) (@lem176219 n p h4)). Qed.
Lemma lem177085 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h7 : Peano.le p n => @lem177084 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176215 p n h6)). Qed.
Lemma lem177086 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177085 p n h1 h2 h3 h4 h5 h6) (@lem176215 p n h6)). Qed.
Lemma lem177087 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term30 n p) = False.
Proof. exact (prop_ext (fun h7 : term30 n p => @lem177086 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176211 n p h5)). Qed.
Lemma lem177088 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177087 p n h1 h2 h3 h4 h5 h6) (@lem176211 n p h5)). Qed.
Lemma lem177089 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : term193 = False.
Proof. exact (prop_ext (fun h7 : term193 => @lem177088 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176107 h3)). Qed.
Lemma lem177090 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177089 p n h1 h2 h3 h4 h5 h6) (@lem176107 h3)). Qed.
Lemma lem177091 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term154 n p) = False.
Proof. exact (prop_ext (fun h7 : term154 n p => @lem177090 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176038 n p h4)). Qed.
Lemma lem177092 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177091 p n h1 h2 h3 h4 h5 h6) (@lem176038 n p h4)). Qed.
Lemma lem177093 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h7 : Peano.le p n => @lem177092 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176026 p n h6)). Qed.
Lemma lem177094 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177093 p n h1 h2 h3 h4 h5 h6) (@lem176026 p n h6)). Qed.
Lemma lem177095 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term30 n p) = False.
Proof. exact (prop_ext (fun h7 : term30 n p => @lem177094 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem176020 n p h5)). Qed.
Lemma lem177096 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177095 p n h1 h2 h3 h4 h5 h6) (@lem176020 n p h5)). Qed.
Lemma lem177097 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : term193 = False.
Proof. exact (prop_ext (fun h7 : term193 => @lem177096 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem175493 h3)). Qed.
Lemma lem177098 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177097 p n h1 h2 h3 h4 h5 h6) (@lem175493 h3)). Qed.
Lemma lem177099 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term154 n p) = False.
Proof. exact (prop_ext (fun h7 : term154 n p => @lem177098 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem175390 n p h4)). Qed.
Lemma lem177100 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177099 p n h1 h2 h3 h4 h5 h6) (@lem175390 n p h4)). Qed.
Lemma lem177101 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (Peano.le p n) = False.
Proof. exact (prop_ext (fun h7 : Peano.le p n => @lem177100 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem175384 p n h6)). Qed.
Lemma lem177102 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177101 p n h1 h2 h3 h4 h5 h6) (@lem175384 p n h6)). Qed.
Lemma lem177103 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : (term30 n p) = False.
Proof. exact (prop_ext (fun h7 : term30 n p => @lem177102 p n h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem175378 n p h5)). Qed.
Lemma lem177104 (p : nat) (n : nat) (h1 : term161) (h2 : term69) (h3 : term193) (h4 : term154 n p) (h5 : term30 n p) (h6 : Peano.le p n) : False.
Proof. exact (EQ_MP (@lem177103 p n h1 h2 h3 h4 h5 h6) (@lem175378 n p h5)). Qed.
Lemma lem177105 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term154 n p) (h4 : term30 n p) (h5 : Peano.le p n) : term159.
Proof. exact (fun h0 : term161 => @lem177104 p n h0 h1 h2 h3 h4 h5). Qed.
Lemma lem177106 : term159 = term160.
Proof. exact (@lem69 term161). Qed.
Lemma lem177107 (p : nat) (n : nat) (h1 : term69) (h2 : term193) (h3 : term154 n p) (h4 : term30 n p) (h5 : Peano.le p n) : term160.
Proof. exact (EQ_MP (@lem177106) (@lem177105 p n h1 h2 h3 h4 h5)). Qed.
Lemma lem177108 (p : nat) (n : nat) (h1 : term193) (h2 : term154 n p) (h3 : term30 n p) (h4 : Peano.le p n) : term164.
Proof. exact (fun h0 : term69 => @lem177107 p n h0 h1 h2 h3 h4). Qed.
Lemma lem177109 (p : nat) (n : nat) (h1 : term154 n p) (h2 : term30 n p) (h3 : Peano.le p n) : term167.
Proof. exact (fun h0 : term193 => @lem177108 p n h0 h1 h2 h3). Qed.
Lemma lem177110 (p : nat) (n : nat) (h1 : term154 n p) (h2 : term30 n p) (h3 : Peano.le p n) : term170.
Proof. exact (fun h0 : term202 => @lem177109 p n h1 h2 h3). Qed.
Lemma lem177111 (p : nat) (n : nat) (h1 : term30 n p) (h2 : Peano.le p n) : term173 n p.
Proof. exact (fun h0 : term154 n p => @lem177110 p n h0 h1 h2). Qed.
Lemma lem177112 (n : nat) (p : nat) (h1 : term30 n p) : term175 n p.
Proof. exact (fun h0 : Peano.le p n => @lem177111 p n h1 h0). Qed.
Lemma lem177113 (n : nat) (p : nat) : term176 n p.
Proof. exact (fun h0 : term30 n p => @lem177112 n p h0). Qed.
Lemma lem177118 (p : nat) : term180 p.
Proof. exact (fun n : nat => @lem177113 n p). Qed.
Lemma lem177123 : term184.
Proof. exact (fun p : nat => @lem177118 p). Qed.
Lemma lem177124 : term183.
Proof. exact (EQ_MP (@lem175365) (@lem177123)). Qed.
Lemma lem177125 (p : nat) : term389 p.
Proof. exact (@lem177124 p). Qed.
Lemma lem177126 (p : nat) : (term389 p) = (term179 p).
Proof. exact (eq_refl (term389 p)). Qed.
Lemma lem177127 (p : nat) : term179 p.
Proof. exact (EQ_MP (@lem177126 p) (@lem177125 p)). Qed.
Lemma lem177128 (p : nat) (n : nat) : term390 p n.
Proof. exact (@lem177127 p n). Qed.
Lemma lem177129 (n : nat) (p : nat) : (term390 p n) = (term155 n p).
Proof. exact (eq_refl (term390 p n)). Qed.
Lemma lem177130 (n : nat) (p : nat) : term155 n p.
Proof. exact (EQ_MP (@lem177129 n p) (@lem177128 p n)). Qed.
Lemma lem177132 (n : nat) (p : nat) : term155 n p.
Proof. exact (@lem175079 n p (@lem177130 n p)). Qed.
Lemma lem177133 (n : nat) (p : nat) (h1 : term30 n p) : term174 n p.
Proof. exact (@lem177132 n p (@lem174210 n p h1)). Qed.
Lemma lem177134 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term172 n p.
Proof. exact (@lem177133 n p h2 (@lem174214 n p h1)). Qed.
Lemma lem177135 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : term169.
Proof. exact (@lem177134 n p h1 h3 (@lem175064 n p h2)). Qed.
Lemma lem177136 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : term166.
Proof. exact (@lem177135 n p h1 h2 h3 (@lem101917)). Qed.
Lemma lem177137 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : term163.
Proof. exact (@lem177136 n p h1 h2 h3 (@lem84996)). Qed.
Lemma lem177138 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : term159.
Proof. exact (@lem177137 n p h1 h2 h3 (@lem136494)). Qed.
Lemma lem177139 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : False.
Proof. exact (@lem177138 n p h1 h2 h3 (@lem101179)). Qed.
Lemma lem177140 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : (term154 n p) = False.
Proof. exact (prop_ext (fun h4 : term154 n p => @lem177139 n p h1 h2 h3) (fun h4 : False => @lem175064 n p h2)). Qed.
Lemma lem177141 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term154 n p) (h3 : term30 n p) : False.
Proof. exact (EQ_MP (@lem177140 n p h1 h2 h3) (@lem175064 n p h2)). Qed.
Lemma lem177142 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term153 n p.
Proof. exact (fun h0 : term154 n p => @lem177141 n p h1 h0 h2). Qed.
Lemma lem177143 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term152 n p.
Proof. exact (EQ_MP (@lem175063 n p) (@lem177142 n p h1 h2)). Qed.
Lemma lem177144 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term391 n p.
Proof. exact (conj (@lem175059 n p h1 h2) (@lem177143 n p h1 h2)). Qed.
Lemma lem177145 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : (term30 n p) = (term391 n p).
Proof. exact (prop_ext (fun h3 : term30 n p => @lem177144 n p h1 h2) (fun h3 : term391 n p => @lem174210 n p h2)). Qed.
Lemma lem177146 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term391 n p.
Proof. exact (EQ_MP (@lem177145 n p h1 h2) (@lem174210 n p h2)). Qed.
Lemma lem177147 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : term392 n p.
Proof. exact (ex_intro (term393 n p) term394 (@lem177146 n p h1 h2)). Qed.
Lemma lem177150 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : (Nat.modulo n p) = (Nat.sub n p).
Proof. exact (@lem174208 n p (@lem177147 n p h1 h2)). Qed.
Lemma lem177151 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : (term8 n p) = ((Nat.modulo n p) = (Nat.sub n p)).
Proof. exact (prop_ext (fun h3 : term8 n p => @lem177150 n p h1 h2) (fun h3 : (Nat.modulo n p) = (Nat.sub n p) => @lem174124 n p h1)). Qed.
Lemma lem177152 (n : nat) (p : nat) (h1 : term8 n p) (h2 : term30 n p) : (Nat.modulo n p) = (Nat.sub n p).
Proof. exact (EQ_MP (@lem177151 n p h1 h2) (@lem174124 n p h1)). Qed.
Lemma lem177153 (n : nat) (p : nat) (h1 : term30 n p) : term41 n p.
Proof. exact (fun h0 : term8 n p => @lem177152 n p h0 h1). Qed.
Lemma lem177154 (n : nat) (p : nat) (h1 : Peano.lt n p) : (Nat.modulo n p) = n.
Proof. exact (EQ_MP (@lem174177 n p h1) (@lem0)). Qed.
Lemma lem177155 (n : nat) (p : nat) (h1 : Peano.lt n p) : (Peano.lt n p) = ((Nat.modulo n p) = n).
Proof. exact (prop_ext (fun h2 : Peano.lt n p => @lem177154 n p h1) (fun h2 : (Nat.modulo n p) = n => @lem174107 n p h1)). Qed.
Lemma lem177156 (n : nat) (p : nat) (h1 : Peano.lt n p) : (Nat.modulo n p) = n.
Proof. exact (EQ_MP (@lem177155 n p h1) (@lem174107 n p h1)). Qed.
Lemma lem177157 (p : nat) (n : nat) : term45 p n.
Proof. exact (fun h0 : Peano.lt n p => @lem177156 n p h0). Qed.
Lemma lem177158 (n : nat) (p : nat) (h1 : term30 n p) : term48 n p.
Proof. exact (conj (@lem177157 p n) (@lem177153 n p h1)). Qed.
Lemma lem177159 (n : nat) (p : nat) (h1 : term30 n p) : (Nat.modulo n p) = (term49 n p).
Proof. exact (EQ_MP (@lem174106 n p) (@lem177158 n p h1)). Qed.
Lemma lem177160 (n : nat) (p : nat) (h1 : term30 n p) : (term30 n p) = ((Nat.modulo n p) = (term49 n p)).
Proof. exact (prop_ext (fun h2 : term30 n p => @lem177159 n p h1) (fun h2 : (Nat.modulo n p) = (term49 n p) => @lem174088 n p h1)). Qed.
Lemma lem177161 (n : nat) (p : nat) (h1 : term30 n p) : (Nat.modulo n p) = (term49 n p).
Proof. exact (EQ_MP (@lem177160 n p h1) (@lem174088 n p h1)). Qed.
Lemma lem177162 (n : nat) (p : nat) : term395 n p.
Proof. exact (fun h0 : term30 n p => @lem177161 n p h0). Qed.
Lemma lem177167 (n : nat) : term396 n.
Proof. exact (fun p : nat => @lem177162 n p). Qed.
Lemma lem177172 : term397.
Proof. exact (fun n : nat => @lem177167 n). Qed.
