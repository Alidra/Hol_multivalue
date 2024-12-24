Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm76380_spec.
Lemma lem79949 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem79950 : term1.
Proof. exact (@lem79949 term2). Qed.
Lemma lem79951 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem79952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem79953 : term6 = term7.
Proof. exact (MK_COMB (@lem79952) (@lem79951)). Qed.
Lemma lem79954 (n : nat) : (term8 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem79955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79956 (n : nat) : (term9 n) = (term10 n).
Proof. exact (MK_COMB (@lem79955) (@lem79954 n)). Qed.
Lemma lem79957 (n : nat) : (term11 n) = ((term12 n) = (term13 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem79958 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem79956 n) (@lem79957 n)). Qed.
Lemma lem79959 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem79958 n)). Qed.
Lemma lem79960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79961 : term18 = term19.
Proof. exact (MK_COMB (@lem79960) (@lem79959)). Qed.
Lemma lem79962 : term20 = term21.
Proof. exact (MK_COMB (@lem79953) (@lem79961)). Qed.
Lemma lem79963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem79964 : term22 = term23.
Proof. exact (MK_COMB (@lem79963) (@lem79962)). Qed.
Lemma lem79965 (n : nat) : (term8 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem79966 : term24 = term2.
Proof. exact (fun_ext (fun n : nat => @lem79965 n)). Qed.
Lemma lem79967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79968 : term25 = term26.
Proof. exact (MK_COMB (@lem79967) (@lem79966)). Qed.
Lemma lem79969 : term1 = term27.
Proof. exact (MK_COMB (@lem79964) (@lem79968)). Qed.
Lemma lem79970 : term27.
Proof. exact (EQ_MP (@lem79969) (@lem79950)). Qed.
Lemma lem79992 : term28.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem79993 (n : nat) : term29 n.
Proof. exact (@lem79992 n). Qed.
Lemma lem79994 (n : nat) : (term29 n) = ((term30 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem80004 : term4 = (NUMERAL 0).
Proof. exact (proj1 (@lem76380)). Qed.
Lemma lem80005 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80006 : term31 = term32.
Proof. exact (MK_COMB (@lem80005) (@lem80004)). Qed.
Lemma lem80008 (n : nat) : (term30 n) = n.
Proof. exact (EQ_MP (@lem79994 n) (@lem79993 n)). Qed.
Lemma lem80009 : term5 = (NUMERAL 0).
Proof. exact (@lem80008 (NUMERAL 0)). Qed.
Lemma lem80010 : (term4 = term5) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem80006) (@lem80009)). Qed.
Lemma lem80012 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80013 (x : nat) : (x = x) = True.
Proof. exact (@lem80012 nat x). Qed.
Lemma lem80014 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem80013 (NUMERAL 0)). Qed.
Lemma lem80015 : (term4 = term5) = True.
Proof. exact (TRANS (@lem80010) (@lem80014)). Qed.
Lemma lem80016 : True = (term4 = term5).
Proof. exact (SYM (@lem80015)). Qed.
Lemma lem80017 : term4 = term5.
Proof. exact (EQ_MP (@lem80016) (@lem0)). Qed.
Lemma lem80018 : term33.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem80019 : term34.
Proof. exact (proj2 (@lem80018)). Qed.
Lemma lem80020 : term35.
Proof. exact (proj2 (@lem80019)). Qed.
Lemma lem80021 (m : nat) : term36 m.
Proof. exact (@lem80020 m). Qed.
Lemma lem80022 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem80023 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem80022 m) (@lem80021 m)). Qed.
Lemma lem80024 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem80023 m n). Qed.
Lemma lem80025 (m : nat) (n : nat) : (term38 m n) = ((term39 m n) = (term40 m n)).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem80027 : term41.
Proof. exact (proj1 (@lem80019)). Qed.
Lemma lem80028 (m : nat) : term42 m.
Proof. exact (@lem80027 m). Qed.
Lemma lem80029 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem80030 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem80029 m) (@lem80028 m)). Qed.
Lemma lem80031 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem80030 m n). Qed.
Lemma lem80032 (m : nat) (n : nat) : (term44 m n) = ((term45 m n) = (term40 m n)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem80042 : term46.
Proof. exact (proj2 (@lem76380)). Qed.
Lemma lem80043 (n : nat) : term47 n.
Proof. exact (@lem80042 n). Qed.
Lemma lem80044 (n : nat) : (term47 n) = ((term12 n) = (term48 n)).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem80050 (n : nat) : (term12 n) = (term48 n).
Proof. exact (EQ_MP (@lem80044 n) (@lem80043 n)). Qed.
Lemma lem80052 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (BIT0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem80053 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80054 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem80053) (@lem80052 n h1)). Qed.
Lemma lem80055 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80056 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (term48 n) = (term51 n).
Proof. exact (MK_COMB (@lem80055) (@lem80054 n h1)). Qed.
Lemma lem80057 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (term12 n) = (term51 n).
Proof. exact (TRANS (@lem80050 n) (@lem80056 n h1)). Qed.
Lemma lem80058 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80059 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (term52 n) = (term53 n).
Proof. exact (MK_COMB (@lem80058) (@lem80057 n h1)). Qed.
Lemma lem80061 (m : nat) (n : nat) : (term45 m n) = (term40 m n).
Proof. exact (EQ_MP (@lem80032 m n) (@lem80031 m n)). Qed.
Lemma lem80062 (n : nat) : (term13 n) = (term54 n).
Proof. exact (@lem80061 n (S n)). Qed.
Lemma lem80064 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (EQ_MP (@lem80025 m n) (@lem80024 m n)). Qed.
Lemma lem80065 (n : nat) : (term55 n) = (term50 n).
Proof. exact (@lem80064 n n). Qed.
Lemma lem80066 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80067 (n : nat) : (term54 n) = (term51 n).
Proof. exact (MK_COMB (@lem80066) (@lem80065 n)). Qed.
Lemma lem80068 (n : nat) : (term13 n) = (term51 n).
Proof. exact (TRANS (@lem80062 n) (@lem80067 n)). Qed.
Lemma lem80069 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : ((term12 n) = (term13 n)) = ((term51 n) = (term51 n)).
Proof. exact (MK_COMB (@lem80059 n h1) (@lem80068 n)). Qed.
Lemma lem80071 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80072 (x : nat) : (x = x) = True.
Proof. exact (@lem80071 nat x). Qed.
Lemma lem80073 (n : nat) : ((term51 n) = (term51 n)) = True.
Proof. exact (@lem80072 (term51 n)). Qed.
Lemma lem80074 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : ((term12 n) = (term13 n)) = True.
Proof. exact (TRANS (@lem80069 n h1) (@lem80073 n)). Qed.
Lemma lem80075 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : True = ((term12 n) = (term13 n)).
Proof. exact (SYM (@lem80074 n h1)). Qed.
Lemma lem80076 (n : nat) (h1 : (BIT0 n) = (Nat.add n n)) : (term12 n) = (term13 n).
Proof. exact (EQ_MP (@lem80075 n h1) (@lem0)). Qed.
Lemma lem80077 (n : nat) : term15 n.
Proof. exact (fun h0 : (BIT0 n) = (Nat.add n n) => @lem80076 n h0). Qed.
Lemma lem80082 : term19.
Proof. exact (fun n : nat => @lem80077 n). Qed.
Lemma lem80083 : term21.
Proof. exact (conj (@lem80017) (@lem80082)). Qed.
Lemma lem80084 : term26.
Proof. exact (@lem79970 (@lem80083)). Qed.
