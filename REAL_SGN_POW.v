Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_POW_term_abbrevs.
Require Import REAL_LT_01_spec.
Require Import REAL_SGN_MUL_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1757962 : term0 = (term0 = True).
Proof. exact (@lem7 term0). Qed.
Lemma lem1757964 (x : real) : term1 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1757965 (x : real) : (term1 x) = ((real_sgn x) = (term2 x)).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1757968 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1757969 (x : real) : term4 x.
Proof. exact (@lem1757968 (term5 x)). Qed.
Lemma lem1757970 (x : real) : (term6 x) = ((term7 x) = (term8 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1757971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1757972 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1757971) (@lem1757970 x)). Qed.
Lemma lem1757973 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1757974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1757975 (x : real) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem1757974) (@lem1757973 x n)). Qed.
Lemma lem1757976 (x : real) (n : nat) : (term16 x n) = ((term17 x n) = (term18 x n)).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1757977 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem1757975 x n) (@lem1757976 x n)). Qed.
Lemma lem1757978 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun n : nat => @lem1757977 x n)). Qed.
Lemma lem1757979 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1757980 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1757979) (@lem1757978 x)). Qed.
Lemma lem1757981 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1757972 x) (@lem1757980 x)). Qed.
Lemma lem1757982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1757983 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1757982) (@lem1757981 x)). Qed.
Lemma lem1757984 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1757985 (x : real) : (term29 x) = (term5 x).
Proof. exact (fun_ext (fun n : nat => @lem1757984 x n)). Qed.
Lemma lem1757986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1757987 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1757986) (@lem1757985 x)). Qed.
Lemma lem1757988 (x : real) : (term4 x) = (term32 x).
Proof. exact (MK_COMB (@lem1757983 x) (@lem1757987 x)). Qed.
Lemma lem1757989 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1757988 x) (@lem1757969 x)). Qed.
Lemma lem1758005 (x : real) : (term33 x) = term34.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1758006 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem1758007 (x : real) : (term7 x) = term35.
Proof. exact (MK_COMB (@lem1758006) (@lem1758005 x)). Qed.
Lemma lem1758008 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1758009 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1758008) (@lem1758007 x)). Qed.
Lemma lem1758011 (x : real) : (term33 x) = term34.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1758012 (x : real) : (term8 x) = term34.
Proof. exact (@lem1758011 (real_sgn x)). Qed.
Lemma lem1758013 (x : real) : ((term7 x) = (term8 x)) = (term35 = term34).
Proof. exact (MK_COMB (@lem1758009 x) (@lem1758012 x)). Qed.
Lemma lem1758016 (x : real) : (term35 = term34) = ((term7 x) = (term8 x)).
Proof. exact (SYM (@lem1758013 x)). Qed.
Lemma lem1758017 (x : real) : term38 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1758018 (x : real) (n : nat) : term39 x n.
Proof. exact (@lem1758017 x n). Qed.
Lemma lem1758019 (x : real) (n : nat) : (term39 x n) = ((term40 x n) = (term41 x n)).
Proof. exact (eq_refl (term39 x n)). Qed.
Lemma lem1758022 (x : real) : term42 x.
Proof. exact (@lem1734254 x). Qed.
Lemma lem1758023 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1758024 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1758023 x) (@lem1758022 x)). Qed.
Lemma lem1758025 (x : real) (y : real) : term44 x y.
Proof. exact (@lem1758024 x y). Qed.
Lemma lem1758026 (x : real) (y : real) : (term44 x y) = ((term45 x y) = (term46 x y)).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1758031 (x : real) (n : nat) : (term40 x n) = (term41 x n).
Proof. exact (EQ_MP (@lem1758019 x n) (@lem1758018 x n)). Qed.
Lemma lem1758032 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem1758033 (x : real) (n : nat) : (term17 x n) = (term47 x n).
Proof. exact (MK_COMB (@lem1758032) (@lem1758031 x n)). Qed.
Lemma lem1758035 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem1758026 x y) (@lem1758025 x y)). Qed.
Lemma lem1758036 (x : real) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (@lem1758035 x (real_pow x n)). Qed.
Lemma lem1758038 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term12 x n) = (term13 x n).
Proof. exact (h1). Qed.
Lemma lem1758039 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1758040 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term48 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem1758039 x) (@lem1758038 x n h1)). Qed.
Lemma lem1758041 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term47 x n) = (term50 x n).
Proof. exact (TRANS (@lem1758036 x n) (@lem1758040 x n h1)). Qed.
Lemma lem1758042 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term17 x n) = (term50 x n).
Proof. exact (TRANS (@lem1758033 x n) (@lem1758041 x n h1)). Qed.
Lemma lem1758043 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1758044 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem1758043) (@lem1758042 x n h1)). Qed.
Lemma lem1758046 (x : real) (n : nat) : (term40 x n) = (term41 x n).
Proof. exact (EQ_MP (@lem1758019 x n) (@lem1758018 x n)). Qed.
Lemma lem1758047 (x : real) (n : nat) : (term18 x n) = (term50 x n).
Proof. exact (@lem1758046 (real_sgn x) n). Qed.
Lemma lem1758048 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : ((term17 x n) = (term18 x n)) = ((term50 x n) = (term50 x n)).
Proof. exact (MK_COMB (@lem1758044 x n h1) (@lem1758047 x n)). Qed.
Lemma lem1758050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1758051 (x : real) : (x = x) = True.
Proof. exact (@lem1758050 real x). Qed.
Lemma lem1758052 (x : real) (n : nat) : ((term50 x n) = (term50 x n)) = True.
Proof. exact (@lem1758051 (term50 x n)). Qed.
Lemma lem1758053 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : ((term17 x n) = (term18 x n)) = True.
Proof. exact (TRANS (@lem1758048 x n h1) (@lem1758052 x n)). Qed.
Lemma lem1758054 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : True = ((term17 x n) = (term18 x n)).
Proof. exact (SYM (@lem1758053 x n h1)). Qed.
Lemma lem1758055 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem1758054 x n h1) (@lem0)). Qed.
Lemma lem1758059 (x : real) : (real_sgn x) = (term2 x).
Proof. exact (EQ_MP (@lem1757965 x) (@lem1757964 x)). Qed.
Lemma lem1758060 : term35 = term53.
Proof. exact (@lem1758059 term34). Qed.
Lemma lem1758062 : term0 = True.
Proof. exact (EQ_MP (@lem1757962) (@lem1499399)). Qed.
Lemma lem1758063 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1758064 : term54 = (@COND real True).
Proof. exact (MK_COMB (@lem1758063) (@lem1758062)). Qed.
Lemma lem1758065 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1758066 : term55 = term56.
Proof. exact (MK_COMB (@lem1758064) (@lem1758065)). Qed.
Lemma lem1758067 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1758068 : term53 = term58.
Proof. exact (MK_COMB (@lem1758066) (@lem1758067)). Qed.
Lemma lem1758070 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1758071 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1758070 real t2 t1). Qed.
Lemma lem1758072 : term58 = term34.
Proof. exact (@lem1758071 term57 term34). Qed.
Lemma lem1758073 : term53 = term34.
Proof. exact (TRANS (@lem1758068) (@lem1758072)). Qed.
Lemma lem1758074 : term35 = term34.
Proof. exact (TRANS (@lem1758060) (@lem1758073)). Qed.
Lemma lem1758075 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1758076 : term37 = term59.
Proof. exact (MK_COMB (@lem1758075) (@lem1758074)). Qed.
Lemma lem1758077 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1758078 : (term35 = term34) = (term34 = term34).
Proof. exact (MK_COMB (@lem1758076) (@lem1758077)). Qed.
Lemma lem1758080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1758081 (x : real) : (x = x) = True.
Proof. exact (@lem1758080 real x). Qed.
Lemma lem1758082 : (term34 = term34) = True.
Proof. exact (@lem1758081 term34). Qed.
Lemma lem1758083 : (term35 = term34) = True.
Proof. exact (TRANS (@lem1758078) (@lem1758082)). Qed.
Lemma lem1758084 : True = (term35 = term34).
Proof. exact (SYM (@lem1758083)). Qed.
Lemma lem1758085 : term35 = term34.
Proof. exact (EQ_MP (@lem1758084) (@lem0)). Qed.
Lemma lem1758086 (x : real) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem1758016 x) (@lem1758085)). Qed.
Lemma lem1758087 (x : real) (n : nat) : term20 x n.
Proof. exact (fun h0 : (term12 x n) = (term13 x n) => @lem1758055 x n h0). Qed.
Lemma lem1758092 (x : real) : term24 x.
Proof. exact (fun n : nat => @lem1758087 x n). Qed.
Lemma lem1758093 (x : real) : term26 x.
Proof. exact (conj (@lem1758086 x) (@lem1758092 x)). Qed.
Lemma lem1758094 (x : real) : term31 x.
Proof. exact (@lem1757989 x (@lem1758093 x)). Qed.
Lemma lem1758099 : term60.
Proof. exact (fun x : real => @lem1758094 x). Qed.
