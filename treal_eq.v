Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_eq_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1326016 : treal_eq = term0.
Proof. exact (@treal_eq_def). Qed.
Lemma lem1326017 (_23683 : prod hreal hreal) : _23683 = _23683.
Proof. exact (eq_refl _23683). Qed.
Lemma lem1326018 (_23683 : prod hreal hreal) : (treal_eq _23683) = (term1 _23683).
Proof. exact (MK_COMB (@lem1326016) (@lem1326017 _23683)). Qed.
Lemma lem1326019 (_23683 : prod hreal hreal) : (term1 _23683) = (term2 _23683).
Proof. exact (eq_refl (term1 _23683)). Qed.
Lemma lem1326020 (_23683 : prod hreal hreal) : (treal_eq _23683) = (term2 _23683).
Proof. exact (TRANS (@lem1326018 _23683) (@lem1326019 _23683)). Qed.
Lemma lem1326021 (_23684 : prod hreal hreal) : _23684 = _23684.
Proof. exact (eq_refl _23684). Qed.
Lemma lem1326022 (_23683 : prod hreal hreal) (_23684 : prod hreal hreal) : (treal_eq _23683 _23684) = (term3 _23683 _23684).
Proof. exact (MK_COMB (@lem1326020 _23683) (@lem1326021 _23684)). Qed.
Lemma lem1326023 (_23684 : prod hreal hreal) (_23683 : prod hreal hreal) : (term3 _23683 _23684) = ((term4 _23683 _23684) = (term4 _23684 _23683)).
Proof. exact (eq_refl (term3 _23683 _23684)). Qed.
Lemma lem1326024 (_23684 : prod hreal hreal) (_23683 : prod hreal hreal) : (treal_eq _23683 _23684) = ((term4 _23683 _23684) = (term4 _23684 _23683)).
Proof. exact (TRANS (@lem1326022 _23683 _23684) (@lem1326023 _23684 _23683)). Qed.
Lemma lem1326025 (_23683 : prod hreal hreal) : term5 _23683.
Proof. exact (fun _23684 : prod hreal hreal => @lem1326024 _23684 _23683). Qed.
Lemma lem1326026 : term6.
Proof. exact (fun _23683 : prod hreal hreal => @lem1326025 _23683). Qed.
Lemma lem1326027 (_23683 : prod hreal hreal) : term7 _23683.
Proof. exact (@lem1326026 _23683). Qed.
Lemma lem1326028 (_23683 : prod hreal hreal) : (term7 _23683) = (term5 _23683).
Proof. exact (eq_refl (term7 _23683)). Qed.
Lemma lem1326029 (_23683 : prod hreal hreal) : term5 _23683.
Proof. exact (EQ_MP (@lem1326028 _23683) (@lem1326027 _23683)). Qed.
Lemma lem1326030 (_23683 : prod hreal hreal) (_23684 : prod hreal hreal) : term8 _23683 _23684.
Proof. exact (@lem1326029 _23683 _23684). Qed.
Lemma lem1326031 (_23684 : prod hreal hreal) (_23683 : prod hreal hreal) : (term8 _23683 _23684) = ((treal_eq _23683 _23684) = ((term4 _23683 _23684) = (term4 _23684 _23683))).
Proof. exact (eq_refl (term8 _23683 _23684)). Qed.
Lemma lem1326032 (_23684 : prod hreal hreal) (_23683 : prod hreal hreal) : (treal_eq _23683 _23684) = ((term4 _23683 _23684) = (term4 _23684 _23683)).
Proof. exact (EQ_MP (@lem1326031 _23684 _23683) (@lem1326030 _23683 _23684)). Qed.
Lemma lem1326033 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)).
Proof. exact (@lem1326032 (@pair hreal hreal x2 y2) (@pair hreal hreal x1 y1)). Qed.
Lemma lem1326034 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1326035 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1326036 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1326035 A B x) (@lem1326034 A B x)). Qed.
Lemma lem1326037 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1326036 A B x y). Qed.
Lemma lem1326038 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((term14 A B x y) = y).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1326040 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1326041 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem1326042 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem1326041 A B x) (@lem1326040 A B x)). Qed.
Lemma lem1326043 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem1326042 A B x y). Qed.
Lemma lem1326044 {A B : Type'} (y : B) (x : A) : (term17 A B x y) = ((term18 A B x y) = x).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem1326047 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1326044 A B y x) (@lem1326043 A B x y)). Qed.
Lemma lem1326048 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1326047 hreal hreal y x). Qed.
Lemma lem1326049 (y1 : hreal) (x1 : hreal) : (term19 x1 y1) = x1.
Proof. exact (@lem1326048 y1 x1). Qed.
Lemma lem1326050 (x1 : hreal) (y1 : hreal) : x1 = (term19 x1 y1).
Proof. exact (SYM (@lem1326049 y1 x1)). Qed.
Lemma lem1326052 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1326038 A B x y) (@lem1326037 A B x y)). Qed.
Lemma lem1326053 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1326052 hreal hreal x y). Qed.
Lemma lem1326054 (x1 : hreal) (y1 : hreal) : (term20 x1 y1) = y1.
Proof. exact (@lem1326053 x1 y1). Qed.
Lemma lem1326055 (x1 : hreal) (y1 : hreal) : y1 = (term20 x1 y1).
Proof. exact (SYM (@lem1326054 x1 y1)). Qed.
Lemma lem1326057 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1326044 A B y x) (@lem1326043 A B x y)). Qed.
Lemma lem1326058 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1326057 hreal hreal y x). Qed.
Lemma lem1326059 (y2 : hreal) (x2 : hreal) : (term19 x2 y2) = x2.
Proof. exact (@lem1326058 y2 x2). Qed.
Lemma lem1326060 (x2 : hreal) (y2 : hreal) : x2 = (term19 x2 y2).
Proof. exact (SYM (@lem1326059 y2 x2)). Qed.
Lemma lem1326062 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1326038 A B x y) (@lem1326037 A B x y)). Qed.
Lemma lem1326063 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1326062 hreal hreal x y). Qed.
Lemma lem1326064 (x2 : hreal) (y2 : hreal) : (term20 x2 y2) = y2.
Proof. exact (@lem1326063 x2 y2). Qed.
Lemma lem1326065 (x2 : hreal) (y2 : hreal) : y2 = (term20 x2 y2).
Proof. exact (SYM (@lem1326064 x2 y2)). Qed.
Lemma lem1326066 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1326067 (x1 : hreal) (y1 : hreal) : (term22 x1) = (term23 x1 y1).
Proof. exact (MK_COMB (@lem1326066) (@lem1326050 x1 y1)). Qed.
Lemma lem1326068 (x1 : hreal) (y1 : hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1326069 (x1 : hreal) : (term25 x1) = (term25 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1326070 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term22 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1326069 x1) (@lem1326068 x1 y1)). Qed.
Lemma lem1326071 (x1 : hreal) : (term22 x1) = (term26 x1).
Proof. exact (eq_refl (term22 x1)). Qed.
Lemma lem1326072 : (@eq (hreal -> hreal -> hreal -> Prop)) = (@eq (hreal -> hreal -> hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> hreal -> Prop))). Qed.
Lemma lem1326073 (x1 : hreal) : (term25 x1) = (term27 x1).
Proof. exact (MK_COMB (@lem1326072) (@lem1326071 x1)). Qed.
Lemma lem1326074 (x1 : hreal) (y1 : hreal) : (term24 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term24 x1 y1)). Qed.
Lemma lem1326075 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term24 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1326073 x1) (@lem1326074 x1 y1)). Qed.
Lemma lem1326076 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (TRANS (@lem1326070 x1 y1) (@lem1326075 x1 y1)). Qed.
Lemma lem1326077 (x1 : hreal) (y1 : hreal) : (term26 x1) = (term24 x1 y1).
Proof. exact (EQ_MP (@lem1326076 x1 y1) (@lem1326067 x1 y1)). Qed.
Lemma lem1326078 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term29 x1 y1).
Proof. exact (MK_COMB (@lem1326077 x1 y1) (@lem1326055 x1 y1)). Qed.
Lemma lem1326079 (x1 : hreal) (y1 : hreal) : (term29 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term29 x1 y1)). Qed.
Lemma lem1326080 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term31 x1 y1).
Proof. exact (eq_refl (term31 x1 y1)). Qed.
Lemma lem1326081 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term28 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1326080 x1 y1) (@lem1326079 x1 y1)). Qed.
Lemma lem1326082 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term32 x1 y1).
Proof. exact (eq_refl (term28 x1 y1)). Qed.
Lemma lem1326083 : (@eq (hreal -> hreal -> Prop)) = (@eq (hreal -> hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> Prop))). Qed.
Lemma lem1326084 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term33 x1 y1).
Proof. exact (MK_COMB (@lem1326083) (@lem1326082 x1 y1)). Qed.
Lemma lem1326085 (x1 : hreal) (y1 : hreal) : (term30 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term30 x1 y1)). Qed.
Lemma lem1326086 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term30 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1326084 x1 y1) (@lem1326085 x1 y1)). Qed.
Lemma lem1326087 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (TRANS (@lem1326081 x1 y1) (@lem1326086 x1 y1)). Qed.
Lemma lem1326088 (x1 : hreal) (y1 : hreal) : (term32 x1 y1) = (term30 x1 y1).
Proof. exact (EQ_MP (@lem1326087 x1 y1) (@lem1326078 x1 y1)). Qed.
Lemma lem1326089 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term34 x1 y1 x2) = (term35 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1326088 x1 y1) (@lem1326060 x2 y2)). Qed.
Lemma lem1326090 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term35 x1 y1 x2 y2) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term35 x1 y1 x2 y2)). Qed.
Lemma lem1326091 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term37 x1 y1 x2) = (term37 x1 y1 x2).
Proof. exact (eq_refl (term37 x1 y1 x2)). Qed.
Lemma lem1326092 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1326091 x1 y1 x2) (@lem1326090 x2 y2 x1 y1)). Qed.
Lemma lem1326093 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term34 x1 y1 x2) = (term38 x1 x2 y1).
Proof. exact (eq_refl (term34 x1 y1 x2)). Qed.
Lemma lem1326094 : (@eq (hreal -> Prop)) = (@eq (hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> Prop))). Qed.
Lemma lem1326095 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term37 x1 y1 x2) = (term39 x1 x2 y1).
Proof. exact (MK_COMB (@lem1326094) (@lem1326093 x1 x2 y1)). Qed.
Lemma lem1326096 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term36 x2 y2 x1 y1) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term36 x2 y2 x1 y1)). Qed.
Lemma lem1326097 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1326095 x1 x2 y1) (@lem1326096 x2 y2 x1 y1)). Qed.
Lemma lem1326098 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (TRANS (@lem1326092 x2 y2 x1 y1) (@lem1326097 x2 y2 x1 y1)). Qed.
Lemma lem1326099 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term38 x1 x2 y1) = (term36 x2 y2 x1 y1).
Proof. exact (EQ_MP (@lem1326098 x2 y2 x1 y1) (@lem1326089 x1 y1 x2 y2)). Qed.
Lemma lem1326100 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1326099 x2 y2 x1 y1) (@lem1326065 x2 y2)). Qed.
Lemma lem1326101 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term41 x1 y1 x2 y2) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)).
Proof. exact (eq_refl (term41 x1 y1 x2 y2)). Qed.
Lemma lem1326102 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term42 x1 x2 y1 y2) = (term42 x1 x2 y1 y2).
Proof. exact (eq_refl (term42 x1 x2 y1 y2)). Qed.
Lemma lem1326103 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = ((term40 x1 x2 y1 y2) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1))).
Proof. exact (MK_COMB (@lem1326102 x1 x2 y1 y2) (@lem1326101 x2 y2 x1 y1)). Qed.
Lemma lem1326104 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 x2 y1 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (eq_refl (term40 x1 x2 y1 y2)). Qed.
Lemma lem1326105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326106 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term42 x1 x2 y1 y2) = (term43 x1 y2 x2 y1).
Proof. exact (MK_COMB (@lem1326105) (@lem1326104 x1 y2 x2 y1)). Qed.
Lemma lem1326107 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)).
Proof. exact (eq_refl ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1))). Qed.
Lemma lem1326108 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1))) = (((hreal_add x1 y2) = (hreal_add x2 y1)) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1))).
Proof. exact (MK_COMB (@lem1326106 x1 y2 x2 y1) (@lem1326107 x2 y2 x1 y1)). Qed.
Lemma lem1326109 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = (((hreal_add x1 y2) = (hreal_add x2 y1)) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1))).
Proof. exact (TRANS (@lem1326103 x2 y2 x1 y1) (@lem1326108 x2 y2 x1 y1)). Qed.
Lemma lem1326110 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((hreal_add x1 y2) = (hreal_add x2 y1)) = ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)).
Proof. exact (EQ_MP (@lem1326109 x2 y2 x1 y1) (@lem1326100 x1 y1 x2 y2)). Qed.
Lemma lem1326111 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : ((term10 x1 y1 x2 y2) = (term10 x2 y2 x1 y1)) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (SYM (@lem1326110 x2 y2 x1 y1)). Qed.
Lemma lem1326112 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (TRANS (@lem1326033 x2 y2 x1 y1) (@lem1326111 x1 y2 x2 y1)). Qed.
Lemma lem1326113 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term44 x1 y2 x2.
Proof. exact (fun y1 : hreal => @lem1326112 x1 y2 x2 y1). Qed.
Lemma lem1326114 (x1 : hreal) (y2 : hreal) : term45 x1 y2.
Proof. exact (fun x2 : hreal => @lem1326113 x1 y2 x2). Qed.
Lemma lem1326115 (x1 : hreal) : term46 x1.
Proof. exact (fun y2 : hreal => @lem1326114 x1 y2). Qed.
Lemma lem1326116 : term47.
Proof. exact (fun x1 : hreal => @lem1326115 x1). Qed.
