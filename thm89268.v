Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89268_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem89019 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem89020 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem89021 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem89020 A B f) (@lem89019 A B f)). Qed.
Lemma lem89022 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem89021 A B f y). Qed.
Lemma lem89023 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem89026 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : le' = (term4 _2237).
Proof. exact (h1). Qed.
Lemma lem89027 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89028 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89026 le' _2237 h1) (@lem89027 m)). Qed.
Lemma lem89030 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89031 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89030 nat (nat -> Prop) f y). Qed.
Lemma lem89032 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (@lem89031 (term4 _2237) m). Qed.
Lemma lem89033 (_2237 : type1605) (_2235 : nat) : (term5 _2237 _2235) = (term8 _2237 _2235).
Proof. exact (eq_refl (term5 _2237 _2235)). Qed.
Lemma lem89034 (_2237 : type1605) : (term9 _2237) = (term4 _2237).
Proof. exact (fun_ext (fun _2235 : nat => @lem89033 _2237 _2235)). Qed.
Lemma lem89035 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89036 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89034 _2237) (@lem89035 m)). Qed.
Lemma lem89037 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89038 (_2237 : type1605) (m : nat) : (term10 _2237 m) = (term11 _2237 m).
Proof. exact (MK_COMB (@lem89037) (@lem89036 _2237 m)). Qed.
Lemma lem89039 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (eq_refl (term5 _2237 m)). Qed.
Lemma lem89040 (_2237 : type1605) (m : nat) : ((term7 _2237 m) = (term5 _2237 m)) = ((term5 _2237 m) = (term8 _2237 m)).
Proof. exact (MK_COMB (@lem89038 _2237 m) (@lem89039 _2237 m)). Qed.
Lemma lem89041 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (EQ_MP (@lem89040 _2237 m) (@lem89032 _2237 m)). Qed.
Lemma lem89042 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term8 _2237 m).
Proof. exact (TRANS (@lem89028 m le' _2237 h1) (@lem89041 _2237 m)). Qed.
Lemma lem89043 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89044 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term12 le' m) = (term13 _2237 m).
Proof. exact (MK_COMB (@lem89042 m le' _2237 h1) (@lem89043)). Qed.
Lemma lem89046 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89047 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89046 nat Prop f y). Qed.
Lemma lem89048 (_2237 : type1605) (m : nat) : (term15 _2237 m) = (term13 _2237 m).
Proof. exact (@lem89047 (term8 _2237 m) (NUMERAL 0)). Qed.
Lemma lem89049 (_2237 : type1605) (_2236 : nat) (m : nat) : (term16 _2237 m _2236) = (_2237 _2236 m).
Proof. exact (eq_refl (term16 _2237 m _2236)). Qed.
Lemma lem89050 (_2237 : type1605) (m : nat) : (term17 _2237 m) = (term8 _2237 m).
Proof. exact (fun_ext (fun _2236 : nat => @lem89049 _2237 _2236 m)). Qed.
Lemma lem89051 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem89052 (_2237 : type1605) (m : nat) : (term15 _2237 m) = (term13 _2237 m).
Proof. exact (MK_COMB (@lem89050 _2237 m) (@lem89051)). Qed.
Lemma lem89053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89054 (_2237 : type1605) (m : nat) : (term18 _2237 m) = (term19 _2237 m).
Proof. exact (MK_COMB (@lem89053) (@lem89052 _2237 m)). Qed.
Lemma lem89055 (_2237 : type1605) (m : nat) : (term13 _2237 m) = (term20 _2237 m).
Proof. exact (eq_refl (term13 _2237 m)). Qed.
Lemma lem89056 (_2237 : type1605) (m : nat) : ((term15 _2237 m) = (term13 _2237 m)) = ((term13 _2237 m) = (term20 _2237 m)).
Proof. exact (MK_COMB (@lem89054 _2237 m) (@lem89055 _2237 m)). Qed.
Lemma lem89057 (_2237 : type1605) (m : nat) : (term13 _2237 m) = (term20 _2237 m).
Proof. exact (EQ_MP (@lem89056 _2237 m) (@lem89048 _2237 m)). Qed.
Lemma lem89058 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term12 le' m) = (term20 _2237 m).
Proof. exact (TRANS (@lem89044 m le' _2237 h1) (@lem89057 _2237 m)). Qed.
Lemma lem89059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89060 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term21 le' m) = (term22 _2237 m).
Proof. exact (MK_COMB (@lem89059) (@lem89058 m le' _2237 h1)). Qed.
Lemma lem89061 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem89062 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : ((term12 le' m) = (m = (NUMERAL 0))) = ((term20 _2237 m) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem89060 m le' _2237 h1) (@lem89061 m)). Qed.
Lemma lem89063 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term23 le') = (term24 _2237).
Proof. exact (fun_ext (fun m : nat => @lem89062 m le' _2237 h1)). Qed.
Lemma lem89064 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89065 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term25 le') = (term26 _2237).
Proof. exact (MK_COMB (@lem89064) (@lem89063 le' _2237 h1)). Qed.
Lemma lem89066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem89067 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term27 le') = (term28 _2237).
Proof. exact (MK_COMB (@lem89066) (@lem89065 le' _2237 h1)). Qed.
Lemma lem89069 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : le' = (term4 _2237).
Proof. exact (h1). Qed.
Lemma lem89070 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89071 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89069 le' _2237 h1) (@lem89070 m)). Qed.
Lemma lem89073 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89074 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89073 nat (nat -> Prop) f y). Qed.
Lemma lem89075 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (@lem89074 (term4 _2237) m). Qed.
Lemma lem89076 (_2237 : type1605) (_2235 : nat) : (term5 _2237 _2235) = (term8 _2237 _2235).
Proof. exact (eq_refl (term5 _2237 _2235)). Qed.
Lemma lem89077 (_2237 : type1605) : (term9 _2237) = (term4 _2237).
Proof. exact (fun_ext (fun _2235 : nat => @lem89076 _2237 _2235)). Qed.
Lemma lem89078 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89079 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89077 _2237) (@lem89078 m)). Qed.
Lemma lem89080 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89081 (_2237 : type1605) (m : nat) : (term10 _2237 m) = (term11 _2237 m).
Proof. exact (MK_COMB (@lem89080) (@lem89079 _2237 m)). Qed.
Lemma lem89082 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (eq_refl (term5 _2237 m)). Qed.
Lemma lem89083 (_2237 : type1605) (m : nat) : ((term7 _2237 m) = (term5 _2237 m)) = ((term5 _2237 m) = (term8 _2237 m)).
Proof. exact (MK_COMB (@lem89081 _2237 m) (@lem89082 _2237 m)). Qed.
Lemma lem89084 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (EQ_MP (@lem89083 _2237 m) (@lem89075 _2237 m)). Qed.
Lemma lem89085 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term8 _2237 m).
Proof. exact (TRANS (@lem89071 m le' _2237 h1) (@lem89084 _2237 m)). Qed.
Lemma lem89086 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89087 (m : nat) (n : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term29 le' m n) = (term30 _2237 m n).
Proof. exact (MK_COMB (@lem89085 m le' _2237 h1) (@lem89086 n)). Qed.
Lemma lem89089 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89090 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89089 nat Prop f y). Qed.
Lemma lem89091 (_2237 : type1605) (m : nat) (n : nat) : (term31 _2237 m n) = (term30 _2237 m n).
Proof. exact (@lem89090 (term8 _2237 m) (S n)). Qed.
Lemma lem89092 (_2237 : type1605) (_2236 : nat) (m : nat) : (term16 _2237 m _2236) = (_2237 _2236 m).
Proof. exact (eq_refl (term16 _2237 m _2236)). Qed.
Lemma lem89093 (_2237 : type1605) (m : nat) : (term17 _2237 m) = (term8 _2237 m).
Proof. exact (fun_ext (fun _2236 : nat => @lem89092 _2237 _2236 m)). Qed.
Lemma lem89094 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem89095 (_2237 : type1605) (m : nat) (n : nat) : (term31 _2237 m n) = (term30 _2237 m n).
Proof. exact (MK_COMB (@lem89093 _2237 m) (@lem89094 n)). Qed.
Lemma lem89096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89097 (_2237 : type1605) (m : nat) (n : nat) : (term32 _2237 m n) = (term33 _2237 m n).
Proof. exact (MK_COMB (@lem89096) (@lem89095 _2237 m n)). Qed.
Lemma lem89098 (_2237 : type1605) (n : nat) (m : nat) : (term30 _2237 m n) = (term34 _2237 n m).
Proof. exact (eq_refl (term30 _2237 m n)). Qed.
Lemma lem89099 (_2237 : type1605) (n : nat) (m : nat) : ((term31 _2237 m n) = (term30 _2237 m n)) = ((term30 _2237 m n) = (term34 _2237 n m)).
Proof. exact (MK_COMB (@lem89097 _2237 m n) (@lem89098 _2237 n m)). Qed.
Lemma lem89100 (_2237 : type1605) (n : nat) (m : nat) : (term30 _2237 m n) = (term34 _2237 n m).
Proof. exact (EQ_MP (@lem89099 _2237 n m) (@lem89091 _2237 m n)). Qed.
Lemma lem89101 (n : nat) (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term29 le' m n) = (term34 _2237 n m).
Proof. exact (TRANS (@lem89087 m n le' _2237 h1) (@lem89100 _2237 n m)). Qed.
Lemma lem89102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89103 (n : nat) (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term35 le' m n) = (term36 _2237 n m).
Proof. exact (MK_COMB (@lem89102) (@lem89101 n m le' _2237 h1)). Qed.
Lemma lem89105 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : le' = (term4 _2237).
Proof. exact (h1). Qed.
Lemma lem89106 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89107 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89105 le' _2237 h1) (@lem89106 m)). Qed.
Lemma lem89109 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89110 (f : type1605) (y : nat) : (term6 f y) = (f y).
Proof. exact (@lem89109 nat (nat -> Prop) f y). Qed.
Lemma lem89111 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (@lem89110 (term4 _2237) m). Qed.
Lemma lem89112 (_2237 : type1605) (_2235 : nat) : (term5 _2237 _2235) = (term8 _2237 _2235).
Proof. exact (eq_refl (term5 _2237 _2235)). Qed.
Lemma lem89113 (_2237 : type1605) : (term9 _2237) = (term4 _2237).
Proof. exact (fun_ext (fun _2235 : nat => @lem89112 _2237 _2235)). Qed.
Lemma lem89114 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89115 (_2237 : type1605) (m : nat) : (term7 _2237 m) = (term5 _2237 m).
Proof. exact (MK_COMB (@lem89113 _2237) (@lem89114 m)). Qed.
Lemma lem89116 : (@eq (nat -> Prop)) = (@eq (nat -> Prop)).
Proof. exact (eq_refl (@eq (nat -> Prop))). Qed.
Lemma lem89117 (_2237 : type1605) (m : nat) : (term10 _2237 m) = (term11 _2237 m).
Proof. exact (MK_COMB (@lem89116) (@lem89115 _2237 m)). Qed.
Lemma lem89118 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (eq_refl (term5 _2237 m)). Qed.
Lemma lem89119 (_2237 : type1605) (m : nat) : ((term7 _2237 m) = (term5 _2237 m)) = ((term5 _2237 m) = (term8 _2237 m)).
Proof. exact (MK_COMB (@lem89117 _2237 m) (@lem89118 _2237 m)). Qed.
Lemma lem89120 (_2237 : type1605) (m : nat) : (term5 _2237 m) = (term8 _2237 m).
Proof. exact (EQ_MP (@lem89119 _2237 m) (@lem89111 _2237 m)). Qed.
Lemma lem89121 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m) = (term8 _2237 m).
Proof. exact (TRANS (@lem89107 m le' _2237 h1) (@lem89120 _2237 m)). Qed.
Lemma lem89122 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89123 (m : nat) (n : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m n) = (term16 _2237 m n).
Proof. exact (MK_COMB (@lem89121 m le' _2237 h1) (@lem89122 n)). Qed.
Lemma lem89125 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem89023 A B f y) (@lem89022 A B f y)). Qed.
Lemma lem89126 (f : nat -> Prop) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem89125 nat Prop f y). Qed.
Lemma lem89127 (_2237 : type1605) (m : nat) (n : nat) : (term37 _2237 m n) = (term16 _2237 m n).
Proof. exact (@lem89126 (term8 _2237 m) n). Qed.
Lemma lem89128 (_2237 : type1605) (_2236 : nat) (m : nat) : (term16 _2237 m _2236) = (_2237 _2236 m).
Proof. exact (eq_refl (term16 _2237 m _2236)). Qed.
Lemma lem89129 (_2237 : type1605) (m : nat) : (term17 _2237 m) = (term8 _2237 m).
Proof. exact (fun_ext (fun _2236 : nat => @lem89128 _2237 _2236 m)). Qed.
Lemma lem89130 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89131 (_2237 : type1605) (m : nat) (n : nat) : (term37 _2237 m n) = (term16 _2237 m n).
Proof. exact (MK_COMB (@lem89129 _2237 m) (@lem89130 n)). Qed.
Lemma lem89132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89133 (_2237 : type1605) (m : nat) (n : nat) : (term38 _2237 m n) = (term39 _2237 m n).
Proof. exact (MK_COMB (@lem89132) (@lem89131 _2237 m n)). Qed.
Lemma lem89134 (_2237 : type1605) (n : nat) (m : nat) : (term16 _2237 m n) = (_2237 n m).
Proof. exact (eq_refl (term16 _2237 m n)). Qed.
Lemma lem89135 (_2237 : type1605) (n : nat) (m : nat) : ((term37 _2237 m n) = (term16 _2237 m n)) = ((term16 _2237 m n) = (_2237 n m)).
Proof. exact (MK_COMB (@lem89133 _2237 m n) (@lem89134 _2237 n m)). Qed.
Lemma lem89136 (_2237 : type1605) (n : nat) (m : nat) : (term16 _2237 m n) = (_2237 n m).
Proof. exact (EQ_MP (@lem89135 _2237 n m) (@lem89127 _2237 m n)). Qed.
Lemma lem89137 (n : nat) (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (le' m n) = (_2237 n m).
Proof. exact (TRANS (@lem89123 m n le' _2237 h1) (@lem89136 _2237 n m)). Qed.
Lemma lem89138 (m : nat) (n : nat) : (term40 m n) = (term40 m n).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem89139 (n : nat) (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term41 le' m n) = (term42 _2237 n m).
Proof. exact (MK_COMB (@lem89138 m n) (@lem89137 n m le' _2237 h1)). Qed.
Lemma lem89140 (n : nat) (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : ((term29 le' m n) = (term41 le' m n)) = ((term34 _2237 n m) = (term42 _2237 n m)).
Proof. exact (MK_COMB (@lem89103 n m le' _2237 h1) (@lem89139 n m le' _2237 h1)). Qed.
Lemma lem89141 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term43 le' m) = (term44 _2237 m).
Proof. exact (fun_ext (fun n : nat => @lem89140 n m le' _2237 h1)). Qed.
Lemma lem89142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89143 (m : nat) (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term45 le' m) = (term46 _2237 m).
Proof. exact (MK_COMB (@lem89142) (@lem89141 m le' _2237 h1)). Qed.
Lemma lem89144 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term47 le') = (term48 _2237).
Proof. exact (fun_ext (fun m : nat => @lem89143 m le' _2237 h1)). Qed.
Lemma lem89145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89146 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term49 le') = (term50 _2237).
Proof. exact (MK_COMB (@lem89145) (@lem89144 le' _2237 h1)). Qed.
Lemma lem89147 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term51 le') = (term52 _2237).
Proof. exact (MK_COMB (@lem89067 le' _2237 h1) (@lem89146 le' _2237 h1)). Qed.
Lemma lem89148 (_2237 : type1605) (h1 : (term53 _2237) = term54) : (term53 _2237) = term54.
Proof. exact (h1). Qed.
Lemma lem89149 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89150 (m : nat) (_2237 : type1605) (h1 : (term53 _2237) = term54) : (term20 _2237 m) = (term55 m).
Proof. exact (MK_COMB (@lem89148 _2237 h1) (@lem89149 m)). Qed.
Lemma lem89151 (m : nat) : (term55 m) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem89152 (_2237 : type1605) (m : nat) : (term22 _2237 m) = (term22 _2237 m).
Proof. exact (eq_refl (term22 _2237 m)). Qed.
Lemma lem89153 (_2237 : type1605) (m : nat) : ((term20 _2237 m) = (term55 m)) = ((term20 _2237 m) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem89152 _2237 m) (@lem89151 m)). Qed.
Lemma lem89154 (m : nat) (_2237 : type1605) (h1 : (term53 _2237) = term54) : (term20 _2237 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem89153 _2237 m) (@lem89150 m _2237 h1)). Qed.
Lemma lem89155 (_2237 : type1605) (h1 : (term53 _2237) = term54) : term26 _2237.
Proof. exact (fun m : nat => @lem89154 m _2237 h1). Qed.
Lemma lem89156 (_2237 : type1605) (h1 : term56 _2237) : term56 _2237.
Proof. exact (h1). Qed.
Lemma lem89157 (n : nat) (_2237 : type1605) (h1 : term56 _2237) : term57 _2237 n.
Proof. exact (@lem89156 _2237 h1 n). Qed.
Lemma lem89158 (_2237 : type1605) (n : nat) : (term57 _2237 n) = ((term58 _2237 n) = (term59 _2237 n)).
Proof. exact (eq_refl (term57 _2237 n)). Qed.
Lemma lem89159 (n : nat) (_2237 : type1605) (h1 : term56 _2237) : (term58 _2237 n) = (term59 _2237 n).
Proof. exact (EQ_MP (@lem89158 _2237 n) (@lem89157 n _2237 h1)). Qed.
Lemma lem89160 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem89161 (n : nat) (m : nat) (_2237 : type1605) (h1 : term56 _2237) : (term34 _2237 n m) = (term60 _2237 n m).
Proof. exact (MK_COMB (@lem89159 n _2237 h1) (@lem89160 m)). Qed.
Lemma lem89162 (_2237 : type1605) (n : nat) (m : nat) : (term60 _2237 n m) = (term42 _2237 n m).
Proof. exact (eq_refl (term60 _2237 n m)). Qed.
Lemma lem89163 (_2237 : type1605) (n : nat) (m : nat) : (term36 _2237 n m) = (term36 _2237 n m).
Proof. exact (eq_refl (term36 _2237 n m)). Qed.
Lemma lem89164 (_2237 : type1605) (n : nat) (m : nat) : ((term34 _2237 n m) = (term60 _2237 n m)) = ((term34 _2237 n m) = (term42 _2237 n m)).
Proof. exact (MK_COMB (@lem89163 _2237 n m) (@lem89162 _2237 n m)). Qed.
Lemma lem89165 (n : nat) (m : nat) (_2237 : type1605) (h1 : term56 _2237) : (term34 _2237 n m) = (term42 _2237 n m).
Proof. exact (EQ_MP (@lem89164 _2237 n m) (@lem89161 n m _2237 h1)). Qed.
Lemma lem89166 (m : nat) (_2237 : type1605) (h1 : term56 _2237) : term46 _2237 m.
Proof. exact (fun n : nat => @lem89165 n m _2237 h1). Qed.
Lemma lem89167 (_2237 : type1605) (h1 : term56 _2237) : term50 _2237.
Proof. exact (fun m : nat => @lem89166 m _2237 h1). Qed.
Lemma lem89168 (_2237 : type1605) (h1 : term61 _2237) : term61 _2237.
Proof. exact (h1). Qed.
Lemma lem89169 (_2237 : type1605) (h1 : term61 _2237) : term56 _2237.
Proof. exact (proj2 (@lem89168 _2237 h1)). Qed.
Lemma lem89170 (_2237 : type1605) (h1 : term61 _2237) : (term53 _2237) = term54.
Proof. exact (proj1 (@lem89168 _2237 h1)). Qed.
Lemma lem89171 (_2237 : type1605) (h1 : term61 _2237) : ((term53 _2237) = term54) = (term26 _2237).
Proof. exact (prop_ext (fun h2 : (term53 _2237) = term54 => @lem89155 _2237 h2) (fun h2 : term26 _2237 => @lem89170 _2237 h1)). Qed.
Lemma lem89172 (_2237 : type1605) (h1 : term61 _2237) : term26 _2237.
Proof. exact (EQ_MP (@lem89171 _2237 h1) (@lem89170 _2237 h1)). Qed.
Lemma lem89173 (_2237 : type1605) (h1 : term61 _2237) : (term56 _2237) = (term50 _2237).
Proof. exact (prop_ext (fun h2 : term56 _2237 => @lem89167 _2237 h2) (fun h2 : term50 _2237 => @lem89169 _2237 h1)). Qed.
Lemma lem89174 (_2237 : type1605) (h1 : term61 _2237) : term50 _2237.
Proof. exact (EQ_MP (@lem89173 _2237 h1) (@lem89169 _2237 h1)). Qed.
Lemma lem89175 (_2237 : type1605) (h1 : term61 _2237) : term52 _2237.
Proof. exact (conj (@lem89172 _2237 h1) (@lem89174 _2237 h1)). Qed.
Lemma lem89176 {A : Type'} (e : A) : term62 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem89177 {A : Type'} (e : A) : (term62 A e) = (term63 A e).
Proof. exact (eq_refl (term62 A e)). Qed.
Lemma lem89178 {A : Type'} (e : A) : term63 A e.
Proof. exact (EQ_MP (@lem89177 A e) (@lem89176 A e)). Qed.
Lemma lem89179 {A : Type'} (e : A) (f : type1423 A) : term64 A e f.
Proof. exact (@lem89178 A e f). Qed.
Lemma lem89180 {A : Type'} (e : A) (f : type1423 A) : (term64 A e f) = (term65 A e f).
Proof. exact (eq_refl (term64 A e f)). Qed.
Lemma lem89181 {A : Type'} (e : A) (f : type1423 A) : term65 A e f.
Proof. exact (EQ_MP (@lem89180 A e f) (@lem89179 A e f)). Qed.
Lemma lem89182 (e : nat -> Prop) (f : type990) : term66 e f.
Proof. exact (@lem89181 (nat -> Prop) e f). Qed.
Lemma lem89183 : term67.
Proof. exact (@lem89182 term54 term68). Qed.
Lemma lem89184 (fn : type1605) (n : nat) : (term69 fn n) = (term70 fn n).
Proof. exact (eq_refl (term69 fn n)). Qed.
Lemma lem89185 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem89186 (fn : type1605) (n : nat) : (term71 fn n) = (term72 fn n).
Proof. exact (MK_COMB (@lem89184 fn n) (@lem89185 n)). Qed.
Lemma lem89187 (fn : type1605) (n : nat) : (term72 fn n) = (term59 fn n).
Proof. exact (eq_refl (term72 fn n)). Qed.
Lemma lem89188 (fn : type1605) (n : nat) : (term71 fn n) = (term59 fn n).
Proof. exact (TRANS (@lem89186 fn n) (@lem89187 fn n)). Qed.
Lemma lem89189 (fn : type1605) (n : nat) : (term73 fn n) = (term73 fn n).
Proof. exact (eq_refl (term73 fn n)). Qed.
Lemma lem89190 (fn : type1605) (n : nat) : ((term58 fn n) = (term71 fn n)) = ((term58 fn n) = (term59 fn n)).
Proof. exact (MK_COMB (@lem89189 fn n) (@lem89188 fn n)). Qed.
Lemma lem89191 (fn : type1605) : (term74 fn) = (term75 fn).
Proof. exact (fun_ext (fun n : nat => @lem89190 fn n)). Qed.
Lemma lem89192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem89193 (fn : type1605) : (term76 fn) = (term56 fn).
Proof. exact (MK_COMB (@lem89192) (@lem89191 fn)). Qed.
Lemma lem89194 (fn : type1605) : (term77 fn) = (term77 fn).
Proof. exact (eq_refl (term77 fn)). Qed.
Lemma lem89195 (fn : type1605) : (term78 fn) = (term61 fn).
Proof. exact (MK_COMB (@lem89194 fn) (@lem89193 fn)). Qed.
Lemma lem89196 : term79 = term80.
Proof. exact (fun_ext (fun fn : type1605 => @lem89195 fn)). Qed.
Lemma lem89197 : (@ex (nat -> nat -> Prop)) = (@ex (nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> Prop))). Qed.
Lemma lem89198 : term67 = term81.
Proof. exact (MK_COMB (@lem89197) (@lem89196)). Qed.
Lemma lem89199 : term81.
Proof. exact (EQ_MP (@lem89198) (@lem89183)). Qed.
Lemma lem89200 (_2237 : type1605) (h1 : term61 _2237) : term61 _2237.
Proof. exact (h1). Qed.
Lemma lem89201 (_2237 : type1605) (h1 : term61 _2237) : term56 _2237.
Proof. exact (proj2 (@lem89200 _2237 h1)). Qed.
Lemma lem89202 (_2237 : type1605) (h1 : term61 _2237) : (term53 _2237) = term54.
Proof. exact (proj1 (@lem89200 _2237 h1)). Qed.
Lemma lem89203 (_2237 : type1605) (h1 : term61 _2237) : term61 _2237.
Proof. exact (conj (@lem89202 _2237 h1) (@lem89201 _2237 h1)). Qed.
Lemma lem89204 (_2237 : type1605) (h1 : term61 _2237) : term81.
Proof. exact (ex_intro term80 _2237 (@lem89203 _2237 h1)). Qed.
Lemma lem89205 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem89206 (h1 : term81) : term81.
Proof. exact (ex_elim (@lem89205 h1) (fun _2237 : type1605 => fun h0 : term80 _2237 => @lem89204 _2237 h0)). Qed.
Lemma lem89207 : term81 = term81.
Proof. exact (prop_ext (fun h1 : term81 => @lem89206 h1) (fun h1 : term81 => @lem89199)). Qed.
Lemma lem89208 : term81.
Proof. exact (EQ_MP (@lem89207) (@lem89199)). Qed.
Lemma lem89209 (_2237 : type1605) (h1 : term61 _2237) : term82.
Proof. exact (ex_intro term83 _2237 (@lem89175 _2237 h1)). Qed.
Lemma lem89210 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem89211 (h1 : term81) : term82.
Proof. exact (ex_elim (@lem89210 h1) (fun _2237 : type1605 => fun h0 : term80 _2237 => @lem89209 _2237 h0)). Qed.
Lemma lem89212 : term81 = term82.
Proof. exact (prop_ext (fun h1 : term81 => @lem89211 h1) (fun h1 : term82 => @lem89208)). Qed.
Lemma lem89213 : term82.
Proof. exact (EQ_MP (@lem89212) (@lem89208)). Qed.
Lemma lem89214 (_2237 : type1605) (h1 : term52 _2237) : term52 _2237.
Proof. exact (h1). Qed.
Lemma lem89215 (le' : type1605) (_2237 : type1605) (h1 : le' = (term4 _2237)) : (term52 _2237) = (term51 le').
Proof. exact (SYM (@lem89147 le' _2237 h1)). Qed.
Lemma lem89216 (le' : type1605) (_2237 : type1605) (h1 : term52 _2237) (h2 : le' = (term4 _2237)) : term51 le'.
Proof. exact (EQ_MP (@lem89215 le' _2237 h2) (@lem89214 _2237 h1)). Qed.
Lemma lem89217 (le' : type1605) (_2237 : type1605) (h1 : term52 _2237) (h2 : le' = (term4 _2237)) : term84.
Proof. exact (ex_intro term85 le' (@lem89216 le' _2237 h1 h2)). Qed.
Lemma lem89218 (_2237 : type1605) : (term4 _2237) = (term4 _2237).
Proof. exact (eq_refl (term4 _2237)). Qed.
Lemma lem89219 (le' : type1605) (_2237 : type1605) (h1 : term52 _2237) : term86 le' _2237.
Proof. exact (fun h0 : le' = (term4 _2237) => @lem89217 le' _2237 h1 h0). Qed.
Lemma lem89220 (_2237 : type1605) (h1 : term52 _2237) : term87 _2237.
Proof. exact (@lem89219 (term4 _2237) _2237 h1). Qed.
Lemma lem89221 (_2237 : type1605) (h1 : term52 _2237) : term84.
Proof. exact (@lem89220 _2237 h1 (@lem89218 _2237)). Qed.
Lemma lem89222 (h1 : term82) : term82.
Proof. exact (h1). Qed.
Lemma lem89223 (h1 : term82) : term84.
Proof. exact (ex_elim (@lem89222 h1) (fun _2237 : type1605 => fun h0 : term83 _2237 => @lem89221 _2237 h0)). Qed.
Lemma lem89224 : term82 = term84.
Proof. exact (prop_ext (fun h1 : term82 => @lem89223 h1) (fun h1 : term84 => @lem89213)). Qed.
Lemma lem89225 : term84.
Proof. exact (EQ_MP (@lem89224) (@lem89213)). Qed.
Lemma lem89226 : term88.
Proof. exact (fun _2241 : prod nat nat => @lem89225). Qed.
Lemma lem89227 {A B : Type'} (P : type1413 A B) : term89 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem89228 {A B : Type'} (P : type1413 A B) : (term89 A B P) = ((term90 A B P) = (term91 A B P)).
Proof. exact (eq_refl (term89 A B P)). Qed.
Lemma lem89231 {A B : Type'} (P : type1413 A B) : (term90 A B P) = (term91 A B P).
Proof. exact (EQ_MP (@lem89228 A B P) (@lem89227 A B P)). Qed.
Lemma lem89232 (P : type1319) : (term92 P) = (term93 P).
Proof. exact (@lem89231 (prod nat nat) type1605 P). Qed.
Lemma lem89233 : term94 = term95.
Proof. exact (@lem89232 term96). Qed.
Lemma lem89234 (_2241 : prod nat nat) : (term97 _2241) = term85.
Proof. exact (eq_refl (term97 _2241)). Qed.
Lemma lem89235 (le' : type1605) : le' = le'.
Proof. exact (eq_refl le'). Qed.
Lemma lem89236 (_2241 : prod nat nat) (le' : type1605) : (term98 _2241 le') = (term99 le').
Proof. exact (MK_COMB (@lem89234 _2241) (@lem89235 le')). Qed.
Lemma lem89237 (le' : type1605) : (term99 le') = (term51 le').
Proof. exact (eq_refl (term99 le')). Qed.
Lemma lem89238 (_2241 : prod nat nat) (le' : type1605) : (term98 _2241 le') = (term51 le').
Proof. exact (TRANS (@lem89236 _2241 le') (@lem89237 le')). Qed.
Lemma lem89239 (_2241 : prod nat nat) : (term100 _2241) = term85.
Proof. exact (fun_ext (fun le' : type1605 => @lem89238 _2241 le')). Qed.
Lemma lem89240 : (@ex (nat -> nat -> Prop)) = (@ex (nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> Prop))). Qed.
Lemma lem89241 (_2241 : prod nat nat) : (term101 _2241) = term84.
Proof. exact (MK_COMB (@lem89240) (@lem89239 _2241)). Qed.
Lemma lem89242 : term102 = term103.
Proof. exact (fun_ext (fun _2241 : prod nat nat => @lem89241 _2241)). Qed.
Lemma lem89243 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem89244 : term94 = term88.
Proof. exact (MK_COMB (@lem89243) (@lem89242)). Qed.
Lemma lem89245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem89246 : term104 = term105.
Proof. exact (MK_COMB (@lem89245) (@lem89244)). Qed.
Lemma lem89247 (_2241 : prod nat nat) : (term97 _2241) = term85.
Proof. exact (eq_refl (term97 _2241)). Qed.
Lemma lem89248 (le' : type1323) (_2241 : prod nat nat) : (le' _2241) = (le' _2241).
Proof. exact (eq_refl (le' _2241)). Qed.
Lemma lem89249 (le' : type1323) (_2241 : prod nat nat) : (term106 le' _2241) = (term107 le' _2241).
Proof. exact (MK_COMB (@lem89247 _2241) (@lem89248 le' _2241)). Qed.
Lemma lem89250 (le' : type1323) (_2241 : prod nat nat) : (term107 le' _2241) = (term108 le' _2241).
Proof. exact (eq_refl (term107 le' _2241)). Qed.
Lemma lem89251 (le' : type1323) (_2241 : prod nat nat) : (term106 le' _2241) = (term108 le' _2241).
Proof. exact (TRANS (@lem89249 le' _2241) (@lem89250 le' _2241)). Qed.
Lemma lem89252 (le' : type1323) : (term109 le') = (term110 le').
Proof. exact (fun_ext (fun _2241 : prod nat nat => @lem89251 le' _2241)). Qed.
Lemma lem89253 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem89254 (le' : type1323) : (term111 le') = (term112 le').
Proof. exact (MK_COMB (@lem89253) (@lem89252 le')). Qed.
Lemma lem89255 : term113 = term114.
Proof. exact (fun_ext (fun le' : type1323 => @lem89254 le')). Qed.
Lemma lem89256 : (@ex ((prod nat nat) -> nat -> nat -> Prop)) = (@ex ((prod nat nat) -> nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat nat) -> nat -> nat -> Prop))). Qed.
Lemma lem89257 : term95 = term115.
Proof. exact (MK_COMB (@lem89256) (@lem89255)). Qed.
Lemma lem89258 : (term94 = term95) = (term88 = term115).
Proof. exact (MK_COMB (@lem89246) (@lem89257)). Qed.
Lemma lem89259 : term88 = term115.
Proof. exact (EQ_MP (@lem89258) (@lem89233)). Qed.
Lemma lem89260 : term115.
Proof. exact (EQ_MP (@lem89259) (@lem89226)). Qed.
Lemma lem89262 {A : Type'} : (@ex A) = (term116 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem89263 : (@ex ((prod nat nat) -> nat -> nat -> Prop)) = term117.
Proof. exact (@lem89262 type1323). Qed.
Lemma lem89264 : term114 = term114.
Proof. exact (eq_refl term114). Qed.
Lemma lem89265 : term115 = term118.
Proof. exact (MK_COMB (@lem89263) (@lem89264)). Qed.
Lemma lem89266 : term118 = term119.
Proof. exact (eq_refl term118). Qed.
Lemma lem89267 : term115 = term119.
Proof. exact (TRANS (@lem89265) (@lem89266)). Qed.
Lemma lem89268 : term119.
Proof. exact (EQ_MP (@lem89267) (@lem89260)). Qed.
