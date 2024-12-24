Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOOSE_SUBSET_EQ_term_abbrevs.
Require Import CARD_SUBSET_spec.
Require Import CHOOSE_SUBSET_STRONG_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4083013 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4083014 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4083015 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4083014 t1) (@lem4083013 t1)). Qed.
Lemma lem4083016 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4083015 t1 t2). Qed.
Lemma lem4083017 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4083018 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4083017 t1 t2) (@lem4083016 t1 t2)). Qed.
Lemma lem4083019 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4083018 t1 t2 t3). Qed.
Lemma lem4083020 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4083021 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4083020 t1 t2 t3) (@lem4083019 t1 t2 t3)). Qed.
Lemma lem4083022 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4083021 t1 t2 t3)). Qed.
Lemma lem4083023 {A : Type'} (n : nat) : term7 A n.
Proof. exact (@lem4083012 A n). Qed.
Lemma lem4083024 {A : Type'} (n : nat) : (term7 A n) = (term8 A n).
Proof. exact (eq_refl (term7 A n)). Qed.
Lemma lem4083025 {A : Type'} (n : nat) : term8 A n.
Proof. exact (EQ_MP (@lem4083024 A n) (@lem4083023 A n)). Qed.
Lemma lem4083026 {A : Type'} (n : nat) (s : A -> Prop) : term9 A n s.
Proof. exact (@lem4083025 A n s). Qed.
Lemma lem4083027 {A : Type'} (s : A -> Prop) (n : nat) : (term9 A n s) = (term10 A s n).
Proof. exact (eq_refl (term9 A n s)). Qed.
Lemma lem4083028 {A : Type'} (s : A -> Prop) (n : nat) : term10 A s n.
Proof. exact (EQ_MP (@lem4083027 A s n) (@lem4083026 A n s)). Qed.
Lemma lem4083029 {A : Type'} (s : A -> Prop) (n : nat) : (term10 A s n) = ((term10 A s n) = True).
Proof. exact (@lem7 (term10 A s n)). Qed.
Lemma lem4083032 {A : Type'} (s : A -> Prop) (n : nat) : (term10 A s n) = True.
Proof. exact (EQ_MP (@lem4083029 A s n) (@lem4083028 A s n)). Qed.
Lemma lem4083033 {A : Type'} (s : A -> Prop) (n : nat) : (term10 A s n) = True.
Proof. exact (@lem4083032 A s n). Qed.
Lemma lem4083034 {A : Type'} (s : A -> Prop) (n : nat) : True = (term10 A s n).
Proof. exact (SYM (@lem4083033 A s n)). Qed.
Lemma lem4083035 {A : Type'} (s : A -> Prop) (n : nat) : term10 A s n.
Proof. exact (EQ_MP (@lem4083034 A s n) (@lem0)). Qed.
Lemma lem4083048 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term11 A s n) : term11 A s n.
Proof. exact (h1). Qed.
Lemma lem4083049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term12 A s t n) : term12 A s t n.
Proof. exact (h1). Qed.
Lemma lem4083050 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4083051 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4083052 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4083053 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem4083054 (m : nat) (h1 : term13) : term14 m.
Proof. exact (@lem4083053 h1 m). Qed.
Lemma lem4083055 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem4083056 (m : nat) (h1 : term13) : term15 m.
Proof. exact (EQ_MP (@lem4083055 m) (@lem4083054 m h1)). Qed.
Lemma lem4083057 (m : nat) (n : nat) (h1 : term13) : term16 m n.
Proof. exact (@lem4083056 m h1 n). Qed.
Lemma lem4083058 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem4083059 (n : nat) (m : nat) (h1 : term13) : term17 n m.
Proof. exact (EQ_MP (@lem4083058 n m) (@lem4083057 m n h1)). Qed.
Lemma lem4083060 (n : nat) (m : nat) (p : nat) (h1 : term13) : term18 n m p.
Proof. exact (@lem4083059 n m h1 p). Qed.
Lemma lem4083061 (n : nat) (m : nat) (p : nat) : (term18 n m p) = (term19 n m p).
Proof. exact (eq_refl (term18 n m p)). Qed.
Lemma lem4083062 (n : nat) (m : nat) (p : nat) (h1 : term13) : term19 n m p.
Proof. exact (EQ_MP (@lem4083061 n m p) (@lem4083060 n m p h1)). Qed.
Lemma lem4083063 (m : nat) (n : nat) (p : nat) (h1 : term20 m n p) : term20 m n p.
Proof. exact (h1). Qed.
Lemma lem4083064 (m : nat) (n : nat) (p : nat) (h1 : term13) (h2 : term20 m n p) : Peano.le m p.
Proof. exact (@lem4083062 n m p h1 (@lem4083063 m n p h2)). Qed.
Lemma lem4083065 (m : nat) (n : nat) (p : nat) (h1 : term20 m n p) : term21 m p.
Proof. exact (fun h0 : term13 => @lem4083064 m n p h0 h1). Qed.
Lemma lem4083066 (m : nat) (p : nat) (h1 : term22 m p) : term22 m p.
Proof. exact (h1). Qed.
Lemma lem4083067 (m : nat) (p : nat) (h1 : term22 m p) : term21 m p.
Proof. exact (ex_elim (@lem4083066 m p h1) (fun n : nat => fun h0 : term23 m p n => @lem4083065 m n p h0)). Qed.
Lemma lem4083068 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem4083069 (m : nat) (p : nat) (h1 : term13) (h2 : term22 m p) : Peano.le m p.
Proof. exact (@lem4083067 m p h2 (@lem4083068 h1)). Qed.
Lemma lem4083070 (m : nat) (p : nat) (h1 : term13) : term24 m p.
Proof. exact (fun h0 : term22 m p => @lem4083069 m p h1 h0). Qed.
Lemma lem4083071 (m : nat) (h1 : term13) : term25 m.
Proof. exact (fun p : nat => @lem4083070 m p h1). Qed.
Lemma lem4083072 (h1 : term13) : term26.
Proof. exact (fun m : nat => @lem4083071 m h1). Qed.
Lemma lem4083073 : term27.
Proof. exact (fun h0 : term13 => @lem4083072 h0). Qed.
Lemma lem4083074 : term26.
Proof. exact (@lem4083073 (@lem93743)). Qed.
Lemma lem4083075 (m : nat) : term28 m.
Proof. exact (@lem4083074 m). Qed.
Lemma lem4083076 (m : nat) : (term28 m) = (term25 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem4083077 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem4083076 m) (@lem4083075 m)). Qed.
Lemma lem4083078 (m : nat) (p : nat) : term29 m p.
Proof. exact (@lem4083077 m p). Qed.
Lemma lem4083079 (m : nat) (p : nat) : (term29 m p) = (term24 m p).
Proof. exact (eq_refl (term29 m p)). Qed.
Lemma lem4083082 (m : nat) (p : nat) : term24 m p.
Proof. exact (EQ_MP (@lem4083079 m p) (@lem4083078 m p)). Qed.
Lemma lem4083083 {A : Type'} (n : nat) (s : A -> Prop) : term30 A n s.
Proof. exact (@lem4083082 n (@CARD A s)). Qed.
Lemma lem4083085 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4083086 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term32 A n t s) = (term33 A n t s).
Proof. exact (@lem4083085 (term32 A n t s)). Qed.
Lemma lem4083087 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term33 A n t s) = (term32 A n t s).
Proof. exact (SYM (@lem4083086 A n t s)). Qed.
Lemma lem4083088 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term34 A n t s) : term34 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083089 {A : Type'} : term35 A.
Proof. exact (@lem3902682 A). Qed.
Lemma lem4083092 {A : Type'} : term36 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem4083097 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term37 A n t s) : term37 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083098 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term38 A n t s.
Proof. exact (fun h0 : term37 A n t s => @lem4083097 A n t s h0). Qed.
Lemma lem4083099 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term38 A n t s) : term38 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083100 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term37 A n t s) : term37 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083101 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term38 A n t s) (h2 : term37 A n t s) : term37 A n t s.
Proof. exact (@lem4083099 A n t s h1 (@lem4083100 A n t s h2)). Qed.
Lemma lem4083102 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term37 A n t s) : term39 A n t s.
Proof. exact (fun h0 : term38 A n t s => @lem4083101 A n t s h0 h1). Qed.
Lemma lem4083103 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term38 A n t s) : term38 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083104 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term38 A n t s) (h2 : term37 A n t s) : term37 A n t s.
Proof. exact (@lem4083102 A n t s h2 (@lem4083103 A n t s h1)). Qed.
Lemma lem4083105 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term38 A n t s) : term38 A n t s.
Proof. exact (fun h0 : term37 A n t s => @lem4083104 A n t s h1 h0). Qed.
Lemma lem4083106 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term40 A n t s.
Proof. exact (fun h0 : term38 A n t s => @lem4083105 A n t s h0). Qed.
Lemma lem4083109 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term38 A n t s.
Proof. exact (@lem4083106 A n t s (@lem4083098 A n t s)). Qed.
Lemma lem4083110 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term38 A n t s.
Proof. exact (@lem4083109 A n t s). Qed.
Lemma lem4083152 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4083153 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (@lem4083152 (term35 A)). Qed.
Lemma lem4083166 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (eq_refl (term43 A)). Qed.
Lemma lem4083167 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (MK_COMB (@lem4083166 A) (@lem4083153 A)). Qed.
Lemma lem4083170 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem4083171 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (MK_COMB (@lem4083170) (@lem4083167 A)). Qed.
Lemma lem4083174 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term49 A n t s) = (term49 A n t s).
Proof. exact (eq_refl (term49 A n t s)). Qed.
Lemma lem4083175 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term50 A n t s) = (term51 A n t s).
Proof. exact (MK_COMB (@lem4083174 A n t s) (@lem4083171 A)). Qed.
Lemma lem4083178 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem4083179 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term53 A n t s) = (term54 A n t s).
Proof. exact (MK_COMB (@lem4083178 A s) (@lem4083175 A n t s)). Qed.
Lemma lem4083182 {A : Type'} (t : A -> Prop) (n : nat) : (term55 A t n) = (term55 A t n).
Proof. exact (eq_refl (term55 A t n)). Qed.
Lemma lem4083183 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term56 A n t s) = (term57 A n t s).
Proof. exact (MK_COMB (@lem4083182 A t n) (@lem4083179 A n t s)). Qed.
Lemma lem4083186 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term58 A t s) = (term58 A t s).
Proof. exact (eq_refl (term58 A t s)). Qed.
Lemma lem4083187 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term37 A n t s) = (term59 A n t s).
Proof. exact (MK_COMB (@lem4083186 A t s) (@lem4083183 A n t s)). Qed.
Lemma lem4083190 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term60 A t s) = (term61 A t s).
Proof. exact (fun_ext (fun n : nat => @lem4083187 A n t s)). Qed.
Lemma lem4083191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083192 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term62 A t s) = (term63 A t s).
Proof. exact (MK_COMB (@lem4083191) (@lem4083190 A t s)). Qed.
Lemma lem4083197 {A : Type'} (s : A -> Prop) : (term64 A s) = (term65 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4083192 A t s)). Qed.
Lemma lem4083198 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083199 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4083198 A) (@lem4083197 A s)). Qed.
Lemma lem4083204 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083199 A s)). Qed.
Lemma lem4083205 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083214 {A : Type'} : (term70 A) = (term71 A).
Proof. exact (MK_COMB (@lem4083205 A) (@lem4083204 A)). Qed.
Lemma lem4083223 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term72 A a b) = (term72 A a b).
Proof. exact (eq_refl (term72 A a b)). Qed.
Lemma lem4083224 {A : Type'} (a : A -> Prop) : (term73 A a) = (term73 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem4083223 A a b)). Qed.
Lemma lem4083225 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083226 {A : Type'} (a : A -> Prop) : (term74 A a) = (term74 A a).
Proof. exact (MK_COMB (@lem4083225 A) (@lem4083224 A a)). Qed.
Lemma lem4083227 {A : Type'} : (term75 A) = (term75 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4083226 A a)). Qed.
Lemma lem4083228 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083229 {A : Type'} : (term35 A) = (term35 A).
Proof. exact (MK_COMB (@lem4083228 A) (@lem4083227 A)). Qed.
Lemma lem4083230 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4083231 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (MK_COMB (@lem4083230) (@lem4083229 A)). Qed.
Lemma lem4083240 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term76 A s n)) = ((@HAS_SIZE A s n) = (term76 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term76 A s n))). Qed.
Lemma lem4083241 {A : Type'} (s : A -> Prop) : (term77 A s) = (term77 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083240 A s n)). Qed.
Lemma lem4083242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083243 {A : Type'} (s : A -> Prop) : (term78 A s) = (term78 A s).
Proof. exact (MK_COMB (@lem4083242) (@lem4083241 A s)). Qed.
Lemma lem4083244 {A : Type'} : (term79 A) = (term79 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083243 A s)). Qed.
Lemma lem4083245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083246 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem4083245 A) (@lem4083244 A)). Qed.
Lemma lem4083247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4083248 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (MK_COMB (@lem4083247) (@lem4083246 A)). Qed.
Lemma lem4083249 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (MK_COMB (@lem4083248 A) (@lem4083231 A)). Qed.
Lemma lem4083250 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem4083251 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem4083250 n)). Qed.
Lemma lem4083252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083253 : term81 = term81.
Proof. exact (MK_COMB (@lem4083252) (@lem4083251)). Qed.
Lemma lem4083254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4083255 : term46 = term46.
Proof. exact (MK_COMB (@lem4083254) (@lem4083253)). Qed.
Lemma lem4083256 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (MK_COMB (@lem4083255) (@lem4083249 A)). Qed.
Lemma lem4083265 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term49 A n t s) = (term49 A n t s).
Proof. exact (eq_refl (term49 A n t s)). Qed.
Lemma lem4083266 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term51 A n t s) = (term51 A n t s).
Proof. exact (MK_COMB (@lem4083265 A n t s) (@lem4083256 A)). Qed.
Lemma lem4083269 {A : Type'} (s : A -> Prop) : (term52 A s) = (term52 A s).
Proof. exact (eq_refl (term52 A s)). Qed.
Lemma lem4083270 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term54 A n t s) = (term54 A n t s).
Proof. exact (MK_COMB (@lem4083269 A s) (@lem4083266 A n t s)). Qed.
Lemma lem4083273 {A : Type'} (t : A -> Prop) (n : nat) : (term55 A t n) = (term55 A t n).
Proof. exact (eq_refl (term55 A t n)). Qed.
Lemma lem4083274 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term57 A n t s) = (term57 A n t s).
Proof. exact (MK_COMB (@lem4083273 A t n) (@lem4083270 A n t s)). Qed.
Lemma lem4083277 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term58 A t s) = (term58 A t s).
Proof. exact (eq_refl (term58 A t s)). Qed.
Lemma lem4083278 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term59 A n t s) = (term59 A n t s).
Proof. exact (MK_COMB (@lem4083277 A t s) (@lem4083274 A n t s)). Qed.
Lemma lem4083279 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term61 A t s) = (term61 A t s).
Proof. exact (fun_ext (fun n : nat => @lem4083278 A n t s)). Qed.
Lemma lem4083280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083281 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term63 A t s).
Proof. exact (MK_COMB (@lem4083280) (@lem4083279 A t s)). Qed.
Lemma lem4083282 {A : Type'} (s : A -> Prop) : (term65 A s) = (term65 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4083281 A t s)). Qed.
Lemma lem4083283 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083284 {A : Type'} (s : A -> Prop) : (term67 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4083283 A) (@lem4083282 A s)). Qed.
Lemma lem4083285 {A : Type'} : (term69 A) = (term69 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083284 A s)). Qed.
Lemma lem4083286 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083287 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (MK_COMB (@lem4083286 A) (@lem4083285 A)). Qed.
Lemma lem4083358 {A : Type'} : (term70 A) = (term71 A).
Proof. exact (TRANS (@lem4083214 A) (@lem4083287 A)). Qed.
Lemma lem4083359 {A : Type'} : (term71 A) = (term70 A).
Proof. exact (SYM (@lem4083358 A)). Qed.
Lemma lem4083363 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term34 A n t s) : term34 A n t s.
Proof. exact (h1). Qed.
Lemma lem4083364 (h1 : term81) : term81.
Proof. exact (h1). Qed.
Lemma lem4083365 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem4083366 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4083372 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4083378 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4083384 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4083395 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term34 A n t s) = (term82 A n t s).
Proof. exact (@lem17045 (term83 A n t) (term84 A t s)). Qed.
Lemma lem4083397 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem4083398 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem4083397 n)). Qed.
Lemma lem4083399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083408 : term81 = term81.
Proof. exact (MK_COMB (@lem4083399) (@lem4083398)). Qed.
Lemma lem4083409 (h1 : term81) : term81.
Proof. exact (EQ_MP (@lem4083408) (@lem4083364 h1)). Qed.
Lemma lem4083420 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term86 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem4083426 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term87 A s n).
Proof. exact (eq_refl (term87 A s n)). Qed.
Lemma lem4083428 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term88 A s n).
Proof. exact (eq_refl (term88 A s n)). Qed.
Lemma lem4083429 {A : Type'} (s : A -> Prop) (n : nat) : (term89 A s n) = (term90 A s n).
Proof. exact (MK_COMB (@lem4083428 A s n) (@lem4083420 A s n)). Qed.
Lemma lem4083430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083431 {A : Type'} (s : A -> Prop) (n : nat) : (term91 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem4083430) (@lem4083429 A s n)). Qed.
Lemma lem4083432 {A : Type'} (s : A -> Prop) (n : nat) : (term93 A s n) = (term94 A s n).
Proof. exact (MK_COMB (@lem4083431 A s n) (@lem4083426 A s n)). Qed.
Lemma lem4083433 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term76 A s n)) = (term93 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term76 A s n)). Qed.
Lemma lem4083434 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term76 A s n)) = (term94 A s n).
Proof. exact (TRANS (@lem4083433 A s n) (@lem4083432 A s n)). Qed.
Lemma lem4083435 {A : Type'} (s : A -> Prop) : (term77 A s) = (term95 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083434 A s n)). Qed.
Lemma lem4083436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083437 {A : Type'} (s : A -> Prop) : (term78 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem4083436) (@lem4083435 A s)). Qed.
Lemma lem4083438 {A : Type'} : (term79 A) = (term97 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083437 A s)). Qed.
Lemma lem4083439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083440 {A : Type'} : (term36 A) = (term98 A).
Proof. exact (MK_COMB (@lem4083439 A) (@lem4083438 A)). Qed.
Lemma lem4083446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4083447 (P : nat -> Prop) (Q : nat -> Prop) : (term101 P Q) = (term102 P Q).
Proof. exact (@lem4083446 nat P Q). Qed.
Lemma lem4083448 {A : Type'} (s : A -> Prop) : (term103 A s) = (term104 A s).
Proof. exact (@lem4083447 (term105 A s) (term106 A s)). Qed.
Lemma lem4083449 {A : Type'} (s : A -> Prop) (n : nat) : (term107 A s n) = (term90 A s n).
Proof. exact (eq_refl (term107 A s n)). Qed.
Lemma lem4083450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083451 {A : Type'} (s : A -> Prop) (n : nat) : (term108 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem4083450) (@lem4083449 A s n)). Qed.
Lemma lem4083452 {A : Type'} (s : A -> Prop) (n : nat) : (term109 A s n) = (term87 A s n).
Proof. exact (eq_refl (term109 A s n)). Qed.
Lemma lem4083453 {A : Type'} (s : A -> Prop) (n : nat) : (term110 A s n) = (term94 A s n).
Proof. exact (MK_COMB (@lem4083451 A s n) (@lem4083452 A s n)). Qed.
Lemma lem4083454 {A : Type'} (s : A -> Prop) : (term111 A s) = (term95 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083453 A s n)). Qed.
Lemma lem4083455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083456 {A : Type'} (s : A -> Prop) : (term103 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem4083455) (@lem4083454 A s)). Qed.
Lemma lem4083457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4083458 {A : Type'} (s : A -> Prop) : (term112 A s) = (term113 A s).
Proof. exact (MK_COMB (@lem4083457) (@lem4083456 A s)). Qed.
Lemma lem4083459 {A : Type'} (s : A -> Prop) (n : nat) : (term107 A s n) = (term90 A s n).
Proof. exact (eq_refl (term107 A s n)). Qed.
Lemma lem4083460 {A : Type'} (s : A -> Prop) : (term114 A s) = (term105 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083459 A s n)). Qed.
Lemma lem4083461 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083462 {A : Type'} (s : A -> Prop) : (term115 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem4083461) (@lem4083460 A s)). Qed.
Lemma lem4083463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083464 {A : Type'} (s : A -> Prop) : (term117 A s) = (term118 A s).
Proof. exact (MK_COMB (@lem4083463) (@lem4083462 A s)). Qed.
Lemma lem4083465 {A : Type'} (s : A -> Prop) (n : nat) : (term109 A s n) = (term87 A s n).
Proof. exact (eq_refl (term109 A s n)). Qed.
Lemma lem4083466 {A : Type'} (s : A -> Prop) : (term119 A s) = (term106 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083465 A s n)). Qed.
Lemma lem4083467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083468 {A : Type'} (s : A -> Prop) : (term120 A s) = (term121 A s).
Proof. exact (MK_COMB (@lem4083467) (@lem4083466 A s)). Qed.
Lemma lem4083469 {A : Type'} (s : A -> Prop) : (term104 A s) = (term122 A s).
Proof. exact (MK_COMB (@lem4083464 A s) (@lem4083468 A s)). Qed.
Lemma lem4083470 {A : Type'} (s : A -> Prop) : ((term103 A s) = (term104 A s)) = ((term96 A s) = (term122 A s)).
Proof. exact (MK_COMB (@lem4083458 A s) (@lem4083469 A s)). Qed.
Lemma lem4083471 {A : Type'} (s : A -> Prop) : (term96 A s) = (term122 A s).
Proof. exact (EQ_MP (@lem4083470 A s) (@lem4083448 A s)). Qed.
Lemma lem4083568 {A : Type'} : (term97 A) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083471 A s)). Qed.
Lemma lem4083569 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083570 {A : Type'} : (term98 A) = (term124 A).
Proof. exact (MK_COMB (@lem4083569 A) (@lem4083568 A)). Qed.
Lemma lem4083572 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4083573 {A : Type'} (P : type686 A) (Q : type686 A) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem4083572 (A -> Prop) P Q). Qed.
Lemma lem4083574 {A : Type'} : (term127 A) = (term128 A).
Proof. exact (@lem4083573 A (term129 A) (term130 A)). Qed.
Lemma lem4083575 {A : Type'} (s : A -> Prop) : (term131 A s) = (term116 A s).
Proof. exact (eq_refl (term131 A s)). Qed.
Lemma lem4083576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083577 {A : Type'} (s : A -> Prop) : (term132 A s) = (term118 A s).
Proof. exact (MK_COMB (@lem4083576) (@lem4083575 A s)). Qed.
Lemma lem4083578 {A : Type'} (s : A -> Prop) : (term133 A s) = (term121 A s).
Proof. exact (eq_refl (term133 A s)). Qed.
Lemma lem4083579 {A : Type'} (s : A -> Prop) : (term134 A s) = (term122 A s).
Proof. exact (MK_COMB (@lem4083577 A s) (@lem4083578 A s)). Qed.
Lemma lem4083580 {A : Type'} : (term135 A) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083579 A s)). Qed.
Lemma lem4083581 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083582 {A : Type'} : (term127 A) = (term124 A).
Proof. exact (MK_COMB (@lem4083581 A) (@lem4083580 A)). Qed.
Lemma lem4083583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4083584 {A : Type'} : (term136 A) = (term137 A).
Proof. exact (MK_COMB (@lem4083583) (@lem4083582 A)). Qed.
Lemma lem4083585 {A : Type'} (s : A -> Prop) : (term131 A s) = (term116 A s).
Proof. exact (eq_refl (term131 A s)). Qed.
Lemma lem4083586 {A : Type'} : (term138 A) = (term129 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083585 A s)). Qed.
Lemma lem4083587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083588 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (MK_COMB (@lem4083587 A) (@lem4083586 A)). Qed.
Lemma lem4083589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083590 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (MK_COMB (@lem4083589) (@lem4083588 A)). Qed.
Lemma lem4083591 {A : Type'} (s : A -> Prop) : (term133 A s) = (term121 A s).
Proof. exact (eq_refl (term133 A s)). Qed.
Lemma lem4083592 {A : Type'} : (term143 A) = (term130 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083591 A s)). Qed.
Lemma lem4083593 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083594 {A : Type'} : (term144 A) = (term145 A).
Proof. exact (MK_COMB (@lem4083593 A) (@lem4083592 A)). Qed.
Lemma lem4083595 {A : Type'} : (term128 A) = (term146 A).
Proof. exact (MK_COMB (@lem4083590 A) (@lem4083594 A)). Qed.
Lemma lem4083596 {A : Type'} : ((term127 A) = (term128 A)) = ((term124 A) = (term146 A)).
Proof. exact (MK_COMB (@lem4083584 A) (@lem4083595 A)). Qed.
Lemma lem4083597 {A : Type'} : (term124 A) = (term146 A).
Proof. exact (EQ_MP (@lem4083596 A) (@lem4083574 A)). Qed.
Lemma lem4083704 {A : Type'} : (term98 A) = (term146 A).
Proof. exact (TRANS (@lem4083570 A) (@lem4083597 A)). Qed.
Lemma lem4083705 {A : Type'} : (term36 A) = (term146 A).
Proof. exact (TRANS (@lem4083440 A) (@lem4083704 A)). Qed.
Lemma lem4083706 {A : Type'} (h1 : term36 A) : term146 A.
Proof. exact (EQ_MP (@lem4083705 A) (@lem4083365 A h1)). Qed.
Lemma lem4083713 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term147 A a b) = (term148 A a b).
Proof. exact (@lem17045 (@SUBSET A a b) (@FINITE A b)). Qed.
Lemma lem4083714 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term84 A a b) = (term84 A a b).
Proof. exact (eq_refl (term84 A a b)). Qed.
Lemma lem4083715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4083716 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term149 A a b) = (term150 A a b).
Proof. exact (MK_COMB (@lem4083715) (@lem4083713 A a b)). Qed.
Lemma lem4083717 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term151 A a b) = (term152 A a b).
Proof. exact (MK_COMB (@lem4083716 A a b) (@lem4083714 A a b)). Qed.
Lemma lem4083718 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term72 A a b) = (term151 A a b).
Proof. exact (@lem17265 (term153 A a b) (term84 A a b)). Qed.
Lemma lem4083719 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term72 A a b) = (term152 A a b).
Proof. exact (TRANS (@lem4083718 A a b) (@lem4083717 A a b)). Qed.
Lemma lem4083720 {A : Type'} (a : A -> Prop) : (term73 A a) = (term154 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem4083719 A a b)). Qed.
Lemma lem4083721 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083722 {A : Type'} (a : A -> Prop) : (term74 A a) = (term155 A a).
Proof. exact (MK_COMB (@lem4083721 A) (@lem4083720 A a)). Qed.
Lemma lem4083723 {A : Type'} : (term75 A) = (term156 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4083722 A a)). Qed.
Lemma lem4083724 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083781 {A : Type'} : (term35 A) = (term157 A).
Proof. exact (MK_COMB (@lem4083724 A) (@lem4083723 A)). Qed.
Lemma lem4083782 {A : Type'} (h1 : term35 A) : term157 A.
Proof. exact (EQ_MP (@lem4083781 A) (@lem4083366 A h1)). Qed.
Lemma lem4083788 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4083794 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4083798 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4083822 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term34 A n t s) : term82 A n t s.
Proof. exact (EQ_MP (@lem4083395 A n t s) (@lem4083363 A n t s h1)). Qed.
Lemma lem4083827 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem4083828 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem4083827 n)). Qed.
Lemma lem4083829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083830 : term81 = term81.
Proof. exact (MK_COMB (@lem4083829) (@lem4083828)). Qed.
Lemma lem4083831 (h1 : term81) : term81.
Proof. exact (EQ_MP (@lem4083830) (@lem4083409 h1)). Qed.
Lemma lem4083854 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term87 A s n).
Proof. exact (eq_refl (term87 A s n)). Qed.
Lemma lem4083855 {A : Type'} (s : A -> Prop) : (term106 A s) = (term106 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083854 A s n)). Qed.
Lemma lem4083856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083857 {A : Type'} (s : A -> Prop) : (term121 A s) = (term121 A s).
Proof. exact (MK_COMB (@lem4083856) (@lem4083855 A s)). Qed.
Lemma lem4083858 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083857 A s)). Qed.
Lemma lem4083859 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083860 {A : Type'} : (term145 A) = (term145 A).
Proof. exact (MK_COMB (@lem4083859 A) (@lem4083858 A)). Qed.
Lemma lem4083885 {A : Type'} (s : A -> Prop) (n : nat) : (term90 A s n) = (term90 A s n).
Proof. exact (eq_refl (term90 A s n)). Qed.
Lemma lem4083886 {A : Type'} (s : A -> Prop) : (term105 A s) = (term105 A s).
Proof. exact (fun_ext (fun n : nat => @lem4083885 A s n)). Qed.
Lemma lem4083887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083888 {A : Type'} (s : A -> Prop) : (term116 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem4083887) (@lem4083886 A s)). Qed.
Lemma lem4083889 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4083888 A s)). Qed.
Lemma lem4083890 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083891 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (MK_COMB (@lem4083890 A) (@lem4083889 A)). Qed.
Lemma lem4083892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4083893 {A : Type'} : (term142 A) = (term142 A).
Proof. exact (MK_COMB (@lem4083892) (@lem4083891 A)). Qed.
Lemma lem4083894 {A : Type'} : (term146 A) = (term146 A).
Proof. exact (MK_COMB (@lem4083893 A) (@lem4083860 A)). Qed.
Lemma lem4083895 {A : Type'} (h1 : term36 A) : term146 A.
Proof. exact (EQ_MP (@lem4083894 A) (@lem4083706 A h1)). Qed.
Lemma lem4083922 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term152 A a b) = (term152 A a b).
Proof. exact (eq_refl (term152 A a b)). Qed.
Lemma lem4083923 {A : Type'} (a : A -> Prop) : (term154 A a) = (term154 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem4083922 A a b)). Qed.
Lemma lem4083924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083925 {A : Type'} (a : A -> Prop) : (term155 A a) = (term155 A a).
Proof. exact (MK_COMB (@lem4083924 A) (@lem4083923 A a)). Qed.
Lemma lem4083926 {A : Type'} : (term156 A) = (term156 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4083925 A a)). Qed.
Lemma lem4083927 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4083928 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (MK_COMB (@lem4083927 A) (@lem4083926 A)). Qed.
Lemma lem4083929 {A : Type'} (h1 : term35 A) : term157 A.
Proof. exact (EQ_MP (@lem4083928 A) (@lem4083782 A h1)). Qed.
Lemma lem4083930 {A : Type'} (h1 : term36 A) : term145 A.
Proof. exact (proj2 (@lem4083895 A h1)). Qed.
Lemma lem4083941 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4083947 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem4083948 : term80 = term80.
Proof. exact (fun_ext (fun n : nat => @lem4083947 n)). Qed.
Lemma lem4083949 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4083951 : term81 = term81.
Proof. exact (MK_COMB (@lem4083949) (@lem4083948)). Qed.
Lemma lem4083952 (h1 : term81) : term81.
Proof. exact (EQ_MP (@lem4083951) (@lem4083831 h1)). Qed.
Lemma lem4084014 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term158 A s n).
Proof. exact (@lem19490 (@FINITE A s) (term159 A s n) ((@CARD A s) = n)). Qed.
Lemma lem4084015 {A : Type'} (s : A -> Prop) : (term106 A s) = (term160 A s).
Proof. exact (fun_ext (fun n : nat => @lem4084014 A s n)). Qed.
Lemma lem4084016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4084017 {A : Type'} (s : A -> Prop) : (term121 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem4084016) (@lem4084015 A s)). Qed.
Lemma lem4084018 {A : Type'} : (term130 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4084017 A s)). Qed.
Lemma lem4084019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4084021 {A : Type'} : (term145 A) = (term163 A).
Proof. exact (MK_COMB (@lem4084019 A) (@lem4084018 A)). Qed.
Lemma lem4084022 {A : Type'} (h1 : term36 A) : term163 A.
Proof. exact (EQ_MP (@lem4084021 A) (@lem4083930 A h1)). Qed.
Lemma lem4084026 {A : Type'} (n : nat) (t : A -> Prop) (h1 : term164 A n t) : term164 A n t.
Proof. exact (h1). Qed.
Lemma lem4084030 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4084038 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4084059 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term152 A a b) = (term152 A a b).
Proof. exact (eq_refl (term152 A a b)). Qed.
Lemma lem4084060 {A : Type'} (a : A -> Prop) : (term154 A a) = (term154 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem4084059 A a b)). Qed.
Lemma lem4084061 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4084062 {A : Type'} (a : A -> Prop) : (term155 A a) = (term155 A a).
Proof. exact (MK_COMB (@lem4084061 A) (@lem4084060 A a)). Qed.
Lemma lem4084063 {A : Type'} : (term156 A) = (term156 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem4084062 A a)). Qed.
Lemma lem4084064 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4084066 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (MK_COMB (@lem4084064 A) (@lem4084063 A)). Qed.
Lemma lem4084067 {A : Type'} (h1 : term35 A) : term157 A.
Proof. exact (EQ_MP (@lem4084066 A) (@lem4083929 A h1)). Qed.
Lemma lem4084119 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term165 A t s) : term165 A t s.
Proof. exact (h1). Qed.
Lemma lem4084120 (_48175 : nat) (h1 : term81) : term166 _48175.
Proof. exact (@lem4083952 h1 _48175). Qed.
Lemma lem4084121 (_48175 : nat) : (term166 _48175) = (Peano.le _48175 _48175).
Proof. exact (eq_refl (term166 _48175)). Qed.
Lemma lem4084135 {A : Type'} (_48180 : A -> Prop) (h1 : term36 A) : term167 A _48180.
Proof. exact (@lem4084022 A h1 _48180). Qed.
Lemma lem4084136 {A : Type'} (_48180 : A -> Prop) : (term167 A _48180) = (term161 A _48180).
Proof. exact (eq_refl (term167 A _48180)). Qed.
Lemma lem4084137 {A : Type'} (_48180 : A -> Prop) (h1 : term36 A) : term161 A _48180.
Proof. exact (EQ_MP (@lem4084136 A _48180) (@lem4084135 A _48180 h1)). Qed.
Lemma lem4084138 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term168 A _48180 _48181.
Proof. exact (@lem4084137 A _48180 h1 _48181). Qed.
Lemma lem4084139 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term168 A _48180 _48181) = (term158 A _48180 _48181).
Proof. exact (eq_refl (term168 A _48180 _48181)). Qed.
Lemma lem4084140 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term158 A _48180 _48181.
Proof. exact (EQ_MP (@lem4084139 A _48180 _48181) (@lem4084138 A _48180 _48181 h1)). Qed.
Lemma lem4084144 {A : Type'} (_48183 : A -> Prop) (h1 : term35 A) : term169 A _48183.
Proof. exact (@lem4084067 A h1 _48183). Qed.
Lemma lem4084145 {A : Type'} (_48183 : A -> Prop) : (term169 A _48183) = (term155 A _48183).
Proof. exact (eq_refl (term169 A _48183)). Qed.
Lemma lem4084146 {A : Type'} (_48183 : A -> Prop) (h1 : term35 A) : term155 A _48183.
Proof. exact (EQ_MP (@lem4084145 A _48183) (@lem4084144 A _48183 h1)). Qed.
Lemma lem4084147 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term170 A _48183 _48184.
Proof. exact (@lem4084146 A _48183 h1 _48184). Qed.
Lemma lem4084148 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term170 A _48183 _48184) = (term152 A _48183 _48184).
Proof. exact (eq_refl (term170 A _48183 _48184)). Qed.
Lemma lem4084149 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term152 A _48183 _48184.
Proof. exact (EQ_MP (@lem4084148 A _48183 _48184) (@lem4084147 A _48183 _48184 h1)). Qed.
Lemma lem4084169 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4084197 {A : Type'} (n : nat) (t : A -> Prop) (h1 : term164 A n t) : term164 A n t.
Proof. exact (h1). Qed.
Lemma lem4084209 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term171 A _48180 _48181.
Proof. exact (proj2 (@lem4084140 A _48180 _48181 h1)). Qed.
Lemma lem4084211 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4084215 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4084228 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term152 A _48183 _48184) = (term172 A _48183 _48184).
Proof. exact (@lem4083022 (term173 A _48183 _48184) (term174 A _48184) (term84 A _48183 _48184)). Qed.
Lemma lem4084229 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term172 A _48183 _48184.
Proof. exact (EQ_MP (@lem4084228 A _48183 _48184) (@lem4084149 A _48183 _48184 h1)). Qed.
Lemma lem4084241 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term165 A t s) : term165 A t s.
Proof. exact (h1). Qed.
Lemma lem4084254 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4084255 (_48189 : nat) (_48191 : nat) (h1 : _48189 = _48191) : _48189 = _48191.
Proof. exact (h1). Qed.
Lemma lem4084256 (_48190 : nat) (_48192 : nat) (h1 : _48190 = _48192) : _48190 = _48192.
Proof. exact (h1). Qed.
Lemma lem4084257 (_48189 : nat) (_48191 : nat) (h1 : _48189 = _48191) : (Peano.le _48189) = (Peano.le _48191).
Proof. exact (MK_COMB (@lem4084254) (@lem4084255 _48189 _48191 h1)). Qed.
Lemma lem4084258 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) (h1 : _48189 = _48191) (h2 : _48190 = _48192) : (Peano.le _48189 _48190) = (Peano.le _48191 _48192).
Proof. exact (MK_COMB (@lem4084257 _48189 _48191 h1) (@lem4084256 _48190 _48192 h2)). Qed.
Lemma lem4084260 (b : Prop) (a : Prop) : term175 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4084261 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : term176 _48191 _48192 _48189 _48190.
Proof. exact (@lem4084260 (Peano.le _48191 _48192) (Peano.le _48189 _48190)). Qed.
Lemma lem4084262 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) (h1 : _48189 = _48191) (h2 : _48190 = _48192) : term177 _48191 _48192 _48189 _48190.
Proof. exact (@lem4084261 _48191 _48192 _48189 _48190 (@lem4084258 _48189 _48191 _48190 _48192 h1 h2)). Qed.
Lemma lem4084263 (_48192 : nat) (_48190 : nat) (_48189 : nat) (_48191 : nat) (h1 : _48189 = _48191) : term178 _48191 _48192 _48189 _48190.
Proof. exact (fun h0 : _48190 = _48192 => @lem4084262 _48189 _48191 _48190 _48192 h1 h0). Qed.
Lemma lem4084265 (a : Prop) (b : Prop) : (a -> b) = (term179 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4084266 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term178 _48191 _48192 _48189 _48190) = (term180 _48191 _48192 _48189 _48190).
Proof. exact (@lem4084265 (_48190 = _48192) (term177 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084267 (_48192 : nat) (_48190 : nat) (_48189 : nat) (_48191 : nat) (h1 : _48189 = _48191) : term180 _48191 _48192 _48189 _48190.
Proof. exact (EQ_MP (@lem4084266 _48191 _48192 _48189 _48190) (@lem4084263 _48192 _48190 _48189 _48191 h1)). Qed.
Lemma lem4084268 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : term181 _48191 _48192 _48189 _48190.
Proof. exact (fun h0 : _48189 = _48191 => @lem4084267 _48192 _48190 _48189 _48191 h0). Qed.
Lemma lem4084270 (a : Prop) (b : Prop) : (a -> b) = (term179 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4084271 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term181 _48191 _48192 _48189 _48190) = (term182 _48191 _48192 _48189 _48190).
Proof. exact (@lem4084270 (_48189 = _48191) (term180 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084272 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : term182 _48191 _48192 _48189 _48190.
Proof. exact (EQ_MP (@lem4084271 _48191 _48192 _48189 _48190) (@lem4084268 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084336 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4084337 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term183 A t n.
Proof. exact (fun h0 : term159 A t n => @lem4084336 A t n h1). Qed.
Lemma lem4084339 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084340 {A : Type'} (t : A -> Prop) (n : nat) : (term183 A t n) = (@HAS_SIZE A t n).
Proof. exact (@lem4084339 (@HAS_SIZE A t n)). Qed.
Lemma lem4084341 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (EQ_MP (@lem4084340 A t n) (@lem4084337 A t n h1)). Qed.
Lemma lem4084347 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4084348 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term171 A _48180 _48181) = (term185 A _48180 _48181).
Proof. exact (@lem4084347 ((@CARD A _48180) = _48181) (term159 A _48180 _48181)). Qed.
Lemma lem4084356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4084357 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term186 A _48180 _48181) = (term187 A _48180 _48181).
Proof. exact (MK_COMB (@lem4084356) (@lem4084348 A _48180 _48181)). Qed.
Lemma lem4084365 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term185 A _48180 _48181) = (term185 A _48180 _48181).
Proof. exact (eq_refl (term185 A _48180 _48181)). Qed.
Lemma lem4084366 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : ((term171 A _48180 _48181) = (term185 A _48180 _48181)) = ((term185 A _48180 _48181) = (term185 A _48180 _48181)).
Proof. exact (MK_COMB (@lem4084357 A _48180 _48181) (@lem4084365 A _48180 _48181)). Qed.
Lemma lem4084368 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4084369 (x : Prop) : (x = x) = True.
Proof. exact (@lem4084368 Prop x). Qed.
Lemma lem4084370 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : ((term185 A _48180 _48181) = (term185 A _48180 _48181)) = True.
Proof. exact (@lem4084369 (term185 A _48180 _48181)). Qed.
Lemma lem4084371 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : ((term171 A _48180 _48181) = (term185 A _48180 _48181)) = True.
Proof. exact (TRANS (@lem4084366 A _48180 _48181) (@lem4084370 A _48180 _48181)). Qed.
Lemma lem4084372 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : True = ((term171 A _48180 _48181) = (term185 A _48180 _48181)).
Proof. exact (SYM (@lem4084371 A _48180 _48181)). Qed.
Lemma lem4084373 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term171 A _48180 _48181) = (term185 A _48180 _48181).
Proof. exact (EQ_MP (@lem4084372 A _48180 _48181) (@lem0)). Qed.
Lemma lem4084374 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term185 A _48180 _48181.
Proof. exact (EQ_MP (@lem4084373 A _48180 _48181) (@lem4084209 A _48180 _48181 h1)). Qed.
Lemma lem4084376 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4084377 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term185 A _48180 _48181) = (term189 A _48180 _48181).
Proof. exact (@lem4084376 (term159 A _48180 _48181) ((@CARD A _48180) = _48181)). Qed.
Lemma lem4084379 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084380 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term191 A _48180 _48181) = (@HAS_SIZE A _48180 _48181).
Proof. exact (@lem4084379 (@HAS_SIZE A _48180 _48181)). Qed.
Lemma lem4084381 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4084382 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term192 A _48180 _48181) = (term55 A _48180 _48181).
Proof. exact (MK_COMB (@lem4084381) (@lem4084380 A _48180 _48181)). Qed.
Lemma lem4084383 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : ((@CARD A _48180) = _48181) = ((@CARD A _48180) = _48181).
Proof. exact (eq_refl ((@CARD A _48180) = _48181)). Qed.
Lemma lem4084384 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term189 A _48180 _48181) = (term193 A _48180 _48181).
Proof. exact (MK_COMB (@lem4084382 A _48180 _48181) (@lem4084383 A _48180 _48181)). Qed.
Lemma lem4084385 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) : (term185 A _48180 _48181) = (term193 A _48180 _48181).
Proof. exact (TRANS (@lem4084377 A _48180 _48181) (@lem4084384 A _48180 _48181)). Qed.
Lemma lem4084388 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term193 A _48180 _48181.
Proof. exact (EQ_MP (@lem4084385 A _48180 _48181) (@lem4084374 A _48180 _48181 h1)). Qed.
Lemma lem4084389 {A : Type'} (_48180 : A -> Prop) (_48181 : nat) (h1 : term36 A) : term193 A _48180 _48181.
Proof. exact (@lem4084388 A _48180 _48181 h1). Qed.
Lemma lem4084390 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) : term193 A t n.
Proof. exact (@lem4084389 A t n h1). Qed.
Lemma lem4084393 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : @HAS_SIZE A t n) : (@CARD A t) = n.
Proof. exact (@lem4084390 A t n h1 (@lem4084341 A t n h2)). Qed.
Lemma lem4084394 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : @HAS_SIZE A t n) : term194 A t n.
Proof. exact (fun h0 : term195 A t n => @lem4084393 A t n h1 h2). Qed.
Lemma lem4084396 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084397 {A : Type'} (t : A -> Prop) (n : nat) : (term194 A t n) = ((@CARD A t) = n).
Proof. exact (@lem4084396 ((@CARD A t) = n)). Qed.
Lemma lem4084398 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : @HAS_SIZE A t n) : (@CARD A t) = n.
Proof. exact (EQ_MP (@lem4084397 A t n) (@lem4084394 A t n h1 h2)). Qed.
Lemma lem4084400 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4084401 {A : Type'} (t : A -> Prop) : (@CARD A t) = (@CARD A t).
Proof. exact (@lem4084400 (@CARD A t)). Qed.
Lemma lem4084402 {A : Type'} (t : A -> Prop) : term196 A t.
Proof. exact (fun h0 : term197 A t => @lem4084401 A t). Qed.
Lemma lem4084404 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084405 {A : Type'} (t : A -> Prop) : (term196 A t) = ((@CARD A t) = (@CARD A t)).
Proof. exact (@lem4084404 ((@CARD A t) = (@CARD A t))). Qed.
Lemma lem4084406 {A : Type'} (t : A -> Prop) : (@CARD A t) = (@CARD A t).
Proof. exact (EQ_MP (@lem4084405 A t) (@lem4084402 A t)). Qed.
Lemma lem4084408 (_48175 : nat) (h1 : term81) : Peano.le _48175 _48175.
Proof. exact (EQ_MP (@lem4084121 _48175) (@lem4084120 _48175 h1)). Qed.
Lemma lem4084409 {A : Type'} (t : A -> Prop) (h1 : term81) : term198 A t.
Proof. exact (@lem4084408 (@CARD A t) h1). Qed.
Lemma lem4084410 {A : Type'} (t : A -> Prop) (h1 : term81) : term199 A t.
Proof. exact (fun h0 : term200 A t => @lem4084409 A t h1). Qed.
Lemma lem4084412 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084413 {A : Type'} (t : A -> Prop) : (term199 A t) = (term198 A t).
Proof. exact (@lem4084412 (term198 A t)). Qed.
Lemma lem4084414 {A : Type'} (t : A -> Prop) (h1 : term81) : term198 A t.
Proof. exact (EQ_MP (@lem4084413 A t) (@lem4084410 A t h1)). Qed.
Lemma lem4084432 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084433 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term180 _48191 _48192 _48189 _48190) = (term201 _48191 _48192 _48189 _48190).
Proof. exact (@lem4084432 (Peano.le _48191 _48192) (term202 _48190 _48192) (term203 _48189 _48190)). Qed.
Lemma lem4084447 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4084448 (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term204 _48192 _48189 _48190) = (term205 _48189 _48190 _48192).
Proof. exact (@lem4084447 (term203 _48189 _48190) (term202 _48190 _48192)). Qed.
Lemma lem4084456 (_48191 : nat) (_48192 : nat) : (term206 _48191 _48192) = (term206 _48191 _48192).
Proof. exact (eq_refl (term206 _48191 _48192)). Qed.
Lemma lem4084457 (_48191 : nat) (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term201 _48191 _48192 _48189 _48190) = (term207 _48191 _48189 _48190 _48192).
Proof. exact (MK_COMB (@lem4084456 _48191 _48192) (@lem4084448 _48189 _48190 _48192)). Qed.
Lemma lem4084468 (_48191 : nat) (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term180 _48191 _48192 _48189 _48190) = (term207 _48191 _48189 _48190 _48192).
Proof. exact (TRANS (@lem4084433 _48191 _48192 _48189 _48190) (@lem4084457 _48191 _48189 _48190 _48192)). Qed.
Lemma lem4084469 (_48189 : nat) (_48191 : nat) : (term208 _48189 _48191) = (term208 _48189 _48191).
Proof. exact (eq_refl (term208 _48189 _48191)). Qed.
Lemma lem4084470 (_48191 : nat) (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term182 _48191 _48192 _48189 _48190) = (term209 _48191 _48189 _48190 _48192).
Proof. exact (MK_COMB (@lem4084469 _48189 _48191) (@lem4084468 _48191 _48189 _48190 _48192)). Qed.
Lemma lem4084474 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084475 (_48191 : nat) (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term209 _48191 _48189 _48190 _48192) = (term210 _48191 _48189 _48190 _48192).
Proof. exact (@lem4084474 (Peano.le _48191 _48192) (term202 _48189 _48191) (term205 _48189 _48190 _48192)). Qed.
Lemma lem4084489 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084490 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term211 _48191 _48189 _48190 _48192) = (term212 _48189 _48191 _48190 _48192).
Proof. exact (@lem4084489 (term203 _48189 _48190) (term202 _48189 _48191) (term202 _48190 _48192)). Qed.
Lemma lem4084510 (_48191 : nat) (_48192 : nat) : (term206 _48191 _48192) = (term206 _48191 _48192).
Proof. exact (eq_refl (term206 _48191 _48192)). Qed.
Lemma lem4084511 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term210 _48191 _48189 _48190 _48192) = (term213 _48189 _48191 _48190 _48192).
Proof. exact (MK_COMB (@lem4084510 _48191 _48192) (@lem4084490 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084522 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term209 _48191 _48189 _48190 _48192) = (term213 _48189 _48191 _48190 _48192).
Proof. exact (TRANS (@lem4084475 _48191 _48189 _48190 _48192) (@lem4084511 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084523 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term182 _48191 _48192 _48189 _48190) = (term213 _48189 _48191 _48190 _48192).
Proof. exact (TRANS (@lem4084470 _48191 _48189 _48190 _48192) (@lem4084522 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4084525 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term214 _48191 _48192 _48189 _48190) = (term215 _48189 _48191 _48190 _48192).
Proof. exact (MK_COMB (@lem4084524) (@lem4084523 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084551 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4084552 (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term204 _48192 _48189 _48190) = (term205 _48189 _48190 _48192).
Proof. exact (@lem4084551 (term203 _48189 _48190) (term202 _48190 _48192)). Qed.
Lemma lem4084560 (_48189 : nat) (_48191 : nat) : (term208 _48189 _48191) = (term208 _48189 _48191).
Proof. exact (eq_refl (term208 _48189 _48191)). Qed.
Lemma lem4084561 (_48191 : nat) (_48189 : nat) (_48190 : nat) (_48192 : nat) : (term216 _48191 _48192 _48189 _48190) = (term211 _48191 _48189 _48190 _48192).
Proof. exact (MK_COMB (@lem4084560 _48189 _48191) (@lem4084552 _48189 _48190 _48192)). Qed.
Lemma lem4084565 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084566 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term211 _48191 _48189 _48190 _48192) = (term212 _48189 _48191 _48190 _48192).
Proof. exact (@lem4084565 (term203 _48189 _48190) (term202 _48189 _48191) (term202 _48190 _48192)). Qed.
Lemma lem4084586 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term216 _48191 _48192 _48189 _48190) = (term212 _48189 _48191 _48190 _48192).
Proof. exact (TRANS (@lem4084561 _48191 _48189 _48190 _48192) (@lem4084566 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084587 (_48191 : nat) (_48192 : nat) : (term206 _48191 _48192) = (term206 _48191 _48192).
Proof. exact (eq_refl (term206 _48191 _48192)). Qed.
Lemma lem4084588 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : (term217 _48191 _48192 _48189 _48190) = (term213 _48189 _48191 _48190 _48192).
Proof. exact (MK_COMB (@lem4084587 _48191 _48192) (@lem4084586 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084599 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : ((term182 _48191 _48192 _48189 _48190) = (term217 _48191 _48192 _48189 _48190)) = ((term213 _48189 _48191 _48190 _48192) = (term213 _48189 _48191 _48190 _48192)).
Proof. exact (MK_COMB (@lem4084525 _48189 _48191 _48190 _48192) (@lem4084588 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084601 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4084602 (x : Prop) : (x = x) = True.
Proof. exact (@lem4084601 Prop x). Qed.
Lemma lem4084603 (_48189 : nat) (_48191 : nat) (_48190 : nat) (_48192 : nat) : ((term213 _48189 _48191 _48190 _48192) = (term213 _48189 _48191 _48190 _48192)) = True.
Proof. exact (@lem4084602 (term213 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084604 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : ((term182 _48191 _48192 _48189 _48190) = (term217 _48191 _48192 _48189 _48190)) = True.
Proof. exact (TRANS (@lem4084599 _48189 _48191 _48190 _48192) (@lem4084603 _48189 _48191 _48190 _48192)). Qed.
Lemma lem4084605 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : True = ((term182 _48191 _48192 _48189 _48190) = (term217 _48191 _48192 _48189 _48190)).
Proof. exact (SYM (@lem4084604 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084606 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term182 _48191 _48192 _48189 _48190) = (term217 _48191 _48192 _48189 _48190).
Proof. exact (EQ_MP (@lem4084605 _48191 _48192 _48189 _48190) (@lem0)). Qed.
Lemma lem4084607 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : term217 _48191 _48192 _48189 _48190.
Proof. exact (EQ_MP (@lem4084606 _48191 _48192 _48189 _48190) (@lem4084272 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084609 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4084610 (_48189 : nat) (_48190 : nat) (_48191 : nat) (_48192 : nat) : (term217 _48191 _48192 _48189 _48190) = (term218 _48189 _48190 _48191 _48192).
Proof. exact (@lem4084609 (term216 _48191 _48192 _48189 _48190) (Peano.le _48191 _48192)). Qed.
Lemma lem4084612 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4084613 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term221 _48191 _48192 _48189 _48190) = (term222 _48191 _48192 _48189 _48190).
Proof. exact (@lem4084612 (term202 _48189 _48191) (term204 _48192 _48189 _48190)). Qed.
Lemma lem4084615 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084616 (_48189 : nat) (_48191 : nat) : (term223 _48189 _48191) = (_48189 = _48191).
Proof. exact (@lem4084615 (_48189 = _48191)). Qed.
Lemma lem4084617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4084618 (_48189 : nat) (_48191 : nat) : (term224 _48189 _48191) = (term225 _48189 _48191).
Proof. exact (MK_COMB (@lem4084617) (@lem4084616 _48189 _48191)). Qed.
Lemma lem4084620 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4084621 (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term226 _48192 _48189 _48190) = (term227 _48192 _48189 _48190).
Proof. exact (@lem4084620 (term202 _48190 _48192) (term203 _48189 _48190)). Qed.
Lemma lem4084623 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084624 (_48190 : nat) (_48192 : nat) : (term223 _48190 _48192) = (_48190 = _48192).
Proof. exact (@lem4084623 (_48190 = _48192)). Qed.
Lemma lem4084625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4084626 (_48190 : nat) (_48192 : nat) : (term224 _48190 _48192) = (term225 _48190 _48192).
Proof. exact (MK_COMB (@lem4084625) (@lem4084624 _48190 _48192)). Qed.
Lemma lem4084628 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084629 (_48189 : nat) (_48190 : nat) : (term228 _48189 _48190) = (Peano.le _48189 _48190).
Proof. exact (@lem4084628 (Peano.le _48189 _48190)). Qed.
Lemma lem4084630 (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term227 _48192 _48189 _48190) = (term229 _48192 _48189 _48190).
Proof. exact (MK_COMB (@lem4084626 _48190 _48192) (@lem4084629 _48189 _48190)). Qed.
Lemma lem4084631 (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term226 _48192 _48189 _48190) = (term229 _48192 _48189 _48190).
Proof. exact (TRANS (@lem4084621 _48192 _48189 _48190) (@lem4084630 _48192 _48189 _48190)). Qed.
Lemma lem4084632 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term222 _48191 _48192 _48189 _48190) = (term230 _48191 _48192 _48189 _48190).
Proof. exact (MK_COMB (@lem4084618 _48189 _48191) (@lem4084631 _48192 _48189 _48190)). Qed.
Lemma lem4084633 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term221 _48191 _48192 _48189 _48190) = (term230 _48191 _48192 _48189 _48190).
Proof. exact (TRANS (@lem4084613 _48191 _48192 _48189 _48190) (@lem4084632 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4084635 (_48191 : nat) (_48192 : nat) (_48189 : nat) (_48190 : nat) : (term231 _48191 _48192 _48189 _48190) = (term232 _48191 _48192 _48189 _48190).
Proof. exact (MK_COMB (@lem4084634) (@lem4084633 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084636 (_48191 : nat) (_48192 : nat) : (Peano.le _48191 _48192) = (Peano.le _48191 _48192).
Proof. exact (eq_refl (Peano.le _48191 _48192)). Qed.
Lemma lem4084637 (_48189 : nat) (_48190 : nat) (_48191 : nat) (_48192 : nat) : (term218 _48189 _48190 _48191 _48192) = (term233 _48189 _48190 _48191 _48192).
Proof. exact (MK_COMB (@lem4084635 _48191 _48192 _48189 _48190) (@lem4084636 _48191 _48192)). Qed.
Lemma lem4084638 (_48189 : nat) (_48190 : nat) (_48191 : nat) (_48192 : nat) : (term217 _48191 _48192 _48189 _48190) = (term233 _48189 _48190 _48191 _48192).
Proof. exact (TRANS (@lem4084610 _48189 _48190 _48191 _48192) (@lem4084637 _48189 _48190 _48191 _48192)). Qed.
Lemma lem4084640 {A : Type'} (t : A -> Prop) (h1 : term81) : term234 A t.
Proof. exact (conj (@lem4084406 A t) (@lem4084414 A t h1)). Qed.
Lemma lem4084641 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : @HAS_SIZE A t n) : term235 A n t.
Proof. exact (conj (@lem4084398 A t n h1 h3) (@lem4084640 A t h2)). Qed.
Lemma lem4084643 (_48189 : nat) (_48190 : nat) (_48191 : nat) (_48192 : nat) : term233 _48189 _48190 _48191 _48192.
Proof. exact (EQ_MP (@lem4084638 _48189 _48190 _48191 _48192) (@lem4084607 _48191 _48192 _48189 _48190)). Qed.
Lemma lem4084644 {A : Type'} (n : nat) (t : A -> Prop) : term236 A n t.
Proof. exact (@lem4084643 (@CARD A t) (@CARD A t) n (@CARD A t)). Qed.
Lemma lem4084647 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : @HAS_SIZE A t n) : term83 A n t.
Proof. exact (@lem4084644 A n t (@lem4084641 A t n h1 h2 h3)). Qed.
Lemma lem4084648 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : @HAS_SIZE A t n) : term237 A n t.
Proof. exact (fun h0 : term164 A n t => @lem4084647 A t n h1 h2 h3). Qed.
Lemma lem4084650 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084651 {A : Type'} (n : nat) (t : A -> Prop) : (term237 A n t) = (term83 A n t).
Proof. exact (@lem4084650 (term83 A n t)). Qed.
Lemma lem4084652 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : @HAS_SIZE A t n) : term83 A n t.
Proof. exact (EQ_MP (@lem4084651 A n t) (@lem4084648 A t n h1 h2 h3)). Qed.
Lemma lem4084655 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4084657 {A : Type'} (n : nat) (t : A -> Prop) : (term164 A n t) = (term238 A n t).
Proof. exact (@lem4084655 (term83 A n t)). Qed.
Lemma lem4084660 {A : Type'} (n : nat) (t : A -> Prop) (h1 : term164 A n t) : term238 A n t.
Proof. exact (EQ_MP (@lem4084657 A n t) (@lem4084197 A n t h1)). Qed.
Lemma lem4084663 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (@lem4084660 A n t h3 (@lem4084652 A t n h1 h2 h4)). Qed.
Lemma lem4084664 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : term239.
Proof. exact (fun h0 : ~ False => @lem4084663 A t n h1 h2 h3 h4). Qed.
Lemma lem4084666 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084667 : term239 = False.
Proof. exact (@lem4084666 False). Qed.
Lemma lem4084668 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084667) (@lem4084664 A t n h1 h2 h3 h4)). Qed.
Lemma lem4084751 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4084752 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : term240 A t s.
Proof. exact (fun h0 : term173 A t s => @lem4084751 A t s h1). Qed.
Lemma lem4084754 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084755 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term240 A t s) = (@SUBSET A t s).
Proof. exact (@lem4084754 (@SUBSET A t s)). Qed.
Lemma lem4084756 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (EQ_MP (@lem4084755 A t s) (@lem4084752 A t s h1)). Qed.
Lemma lem4084758 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4084759 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term241 A s.
Proof. exact (fun h0 : term174 A s => @lem4084758 A s h1). Qed.
Lemma lem4084761 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084762 {A : Type'} (s : A -> Prop) : (term241 A s) = (@FINITE A s).
Proof. exact (@lem4084761 (@FINITE A s)). Qed.
Lemma lem4084763 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4084762 A s) (@lem4084759 A s h1)). Qed.
Lemma lem4084769 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084770 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term172 A _48183 _48184) = (term242 A _48183 _48184).
Proof. exact (@lem4084769 (term174 A _48184) (term173 A _48183 _48184) (term84 A _48183 _48184)). Qed.
Lemma lem4084784 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4084785 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term243 A _48183 _48184) = (term244 A _48183 _48184).
Proof. exact (@lem4084784 (term84 A _48183 _48184) (term173 A _48183 _48184)). Qed.
Lemma lem4084791 {A : Type'} (_48184 : A -> Prop) : (term245 A _48184) = (term245 A _48184).
Proof. exact (eq_refl (term245 A _48184)). Qed.
Lemma lem4084792 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term242 A _48183 _48184) = (term246 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084791 A _48184) (@lem4084785 A _48183 _48184)). Qed.
Lemma lem4084796 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4084797 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term246 A _48183 _48184) = (term247 A _48183 _48184).
Proof. exact (@lem4084796 (term84 A _48183 _48184) (term174 A _48184) (term173 A _48183 _48184)). Qed.
Lemma lem4084813 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term242 A _48183 _48184) = (term247 A _48183 _48184).
Proof. exact (TRANS (@lem4084792 A _48183 _48184) (@lem4084797 A _48183 _48184)). Qed.
Lemma lem4084814 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term172 A _48183 _48184) = (term247 A _48183 _48184).
Proof. exact (TRANS (@lem4084770 A _48183 _48184) (@lem4084813 A _48183 _48184)). Qed.
Lemma lem4084815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4084816 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term248 A _48183 _48184) = (term249 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084815) (@lem4084814 A _48183 _48184)). Qed.
Lemma lem4084830 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4084831 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term148 A _48183 _48184) = (term250 A _48183 _48184).
Proof. exact (@lem4084830 (term174 A _48184) (term173 A _48183 _48184)). Qed.
Lemma lem4084837 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term251 A _48183 _48184) = (term251 A _48183 _48184).
Proof. exact (eq_refl (term251 A _48183 _48184)). Qed.
Lemma lem4084838 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term252 A _48183 _48184) = (term247 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084837 A _48183 _48184) (@lem4084831 A _48183 _48184)). Qed.
Lemma lem4084849 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : ((term172 A _48183 _48184) = (term252 A _48183 _48184)) = ((term247 A _48183 _48184) = (term247 A _48183 _48184)).
Proof. exact (MK_COMB (@lem4084816 A _48183 _48184) (@lem4084838 A _48183 _48184)). Qed.
Lemma lem4084851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4084852 (x : Prop) : (x = x) = True.
Proof. exact (@lem4084851 Prop x). Qed.
Lemma lem4084853 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : ((term247 A _48183 _48184) = (term247 A _48183 _48184)) = True.
Proof. exact (@lem4084852 (term247 A _48183 _48184)). Qed.
Lemma lem4084854 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : ((term172 A _48183 _48184) = (term252 A _48183 _48184)) = True.
Proof. exact (TRANS (@lem4084849 A _48183 _48184) (@lem4084853 A _48183 _48184)). Qed.
Lemma lem4084855 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : True = ((term172 A _48183 _48184) = (term252 A _48183 _48184)).
Proof. exact (SYM (@lem4084854 A _48183 _48184)). Qed.
Lemma lem4084856 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term172 A _48183 _48184) = (term252 A _48183 _48184).
Proof. exact (EQ_MP (@lem4084855 A _48183 _48184) (@lem0)). Qed.
Lemma lem4084857 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term252 A _48183 _48184.
Proof. exact (EQ_MP (@lem4084856 A _48183 _48184) (@lem4084229 A _48183 _48184 h1)). Qed.
Lemma lem4084859 (b : Prop) (a : Prop) : (a \/ b) = (term188 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4084860 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term252 A _48183 _48184) = (term253 A _48183 _48184).
Proof. exact (@lem4084859 (term148 A _48183 _48184) (term84 A _48183 _48184)). Qed.
Lemma lem4084862 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4084863 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term254 A _48183 _48184) = (term255 A _48183 _48184).
Proof. exact (@lem4084862 (term173 A _48183 _48184) (term174 A _48184)). Qed.
Lemma lem4084865 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084866 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term256 A _48183 _48184) = (@SUBSET A _48183 _48184).
Proof. exact (@lem4084865 (@SUBSET A _48183 _48184)). Qed.
Lemma lem4084867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4084868 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term257 A _48183 _48184) = (term258 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084867) (@lem4084866 A _48183 _48184)). Qed.
Lemma lem4084870 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4084871 {A : Type'} (_48184 : A -> Prop) : (term259 A _48184) = (@FINITE A _48184).
Proof. exact (@lem4084870 (@FINITE A _48184)). Qed.
Lemma lem4084872 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term255 A _48183 _48184) = (term153 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084868 A _48183 _48184) (@lem4084871 A _48184)). Qed.
Lemma lem4084873 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term254 A _48183 _48184) = (term153 A _48183 _48184).
Proof. exact (TRANS (@lem4084863 A _48183 _48184) (@lem4084872 A _48183 _48184)). Qed.
Lemma lem4084874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4084875 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term260 A _48183 _48184) = (term261 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084874) (@lem4084873 A _48183 _48184)). Qed.
Lemma lem4084876 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term84 A _48183 _48184) = (term84 A _48183 _48184).
Proof. exact (eq_refl (term84 A _48183 _48184)). Qed.
Lemma lem4084877 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term253 A _48183 _48184) = (term72 A _48183 _48184).
Proof. exact (MK_COMB (@lem4084875 A _48183 _48184) (@lem4084876 A _48183 _48184)). Qed.
Lemma lem4084878 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) : (term252 A _48183 _48184) = (term72 A _48183 _48184).
Proof. exact (TRANS (@lem4084860 A _48183 _48184) (@lem4084877 A _48183 _48184)). Qed.
Lemma lem4084880 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @SUBSET A t s) : term153 A t s.
Proof. exact (conj (@lem4084756 A t s h2) (@lem4084763 A s h1)). Qed.
Lemma lem4084882 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term72 A _48183 _48184.
Proof. exact (EQ_MP (@lem4084878 A _48183 _48184) (@lem4084857 A _48183 _48184 h1)). Qed.
Lemma lem4084883 {A : Type'} (_48183 : A -> Prop) (_48184 : A -> Prop) (h1 : term35 A) : term72 A _48183 _48184.
Proof. exact (@lem4084882 A _48183 _48184 h1). Qed.
Lemma lem4084884 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) : term72 A t s.
Proof. exact (@lem4084883 A t s h1). Qed.
Lemma lem4084887 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : @SUBSET A t s) : term84 A t s.
Proof. exact (@lem4084884 A t s h1 (@lem4084880 A t s h2 h3)). Qed.
Lemma lem4084888 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : @SUBSET A t s) : term262 A t s.
Proof. exact (fun h0 : term165 A t s => @lem4084887 A t s h1 h2 h3). Qed.
Lemma lem4084890 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084891 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term262 A t s) = (term84 A t s).
Proof. exact (@lem4084890 (term84 A t s)). Qed.
Lemma lem4084892 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : @SUBSET A t s) : term84 A t s.
Proof. exact (EQ_MP (@lem4084891 A t s) (@lem4084888 A t s h1 h2 h3)). Qed.
Lemma lem4084895 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4084897 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term165 A t s) = (term263 A t s).
Proof. exact (@lem4084895 (term84 A t s)). Qed.
Lemma lem4084900 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term165 A t s) : term263 A t s.
Proof. exact (EQ_MP (@lem4084897 A t s) (@lem4084241 A t s h1)). Qed.
Lemma lem4084903 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (@lem4084900 A t s h3 (@lem4084892 A t s h1 h2 h4)). Qed.
Lemma lem4084904 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : term239.
Proof. exact (fun h0 : ~ False => @lem4084903 A t s h1 h2 h3 h4). Qed.
Lemma lem4084906 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4084907 : term239 = False.
Proof. exact (@lem4084906 False). Qed.
Lemma lem4084908 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084907) (@lem4084904 A t s h1 h2 h3 h4)). Qed.
Lemma lem4084909 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (term165 A t s) = False.
Proof. exact (prop_ext (fun h5 : term165 A t s => @lem4084908 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084241 A t s h3)). Qed.
Lemma lem4084910 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084909 A t s h1 h2 h3 h4) (@lem4084241 A t s h3)). Qed.
Lemma lem4084911 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4084910 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084215 A s h2)). Qed.
Lemma lem4084912 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084911 A t s h1 h2 h3 h4) (@lem4084215 A s h2)). Qed.
Lemma lem4084913 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@SUBSET A t s) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A t s => @lem4084912 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084211 A t s h4)). Qed.
Lemma lem4084914 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084913 A t s h1 h2 h3 h4) (@lem4084211 A t s h4)). Qed.
Lemma lem4084915 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (term164 A n t) = False.
Proof. exact (prop_ext (fun h5 : term164 A n t => @lem4084668 A t n h1 h2 h3 h4) (fun h5 : False => @lem4084197 A n t h3)). Qed.
Lemma lem4084916 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084915 A t n h1 h2 h3 h4) (@lem4084197 A n t h3)). Qed.
Lemma lem4084917 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (@HAS_SIZE A t n) = False.
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A t n => @lem4084916 A t n h1 h2 h3 h4) (fun h5 : False => @lem4084169 A t n h4)). Qed.
Lemma lem4084918 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084917 A t n h1 h2 h3 h4) (@lem4084169 A t n h4)). Qed.
Lemma lem4084919 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (term165 A t s) = False.
Proof. exact (prop_ext (fun h5 : term165 A t s => @lem4084914 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084119 A t s h3)). Qed.
Lemma lem4084920 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084919 A t s h1 h2 h3 h4) (@lem4084119 A t s h3)). Qed.
Lemma lem4084921 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4084920 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084038 A s h2)). Qed.
Lemma lem4084922 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084921 A t s h1 h2 h3 h4) (@lem4084038 A s h2)). Qed.
Lemma lem4084923 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@SUBSET A t s) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A t s => @lem4084922 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084030 A t s h4)). Qed.
Lemma lem4084924 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084923 A t s h1 h2 h3 h4) (@lem4084030 A t s h4)). Qed.
Lemma lem4084925 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (term164 A n t) = False.
Proof. exact (prop_ext (fun h5 : term164 A n t => @lem4084918 A t n h1 h2 h3 h4) (fun h5 : False => @lem4084026 A n t h3)). Qed.
Lemma lem4084926 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084925 A t n h1 h2 h3 h4) (@lem4084026 A n t h3)). Qed.
Lemma lem4084927 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (@HAS_SIZE A t n) = False.
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A t n => @lem4084926 A t n h1 h2 h3 h4) (fun h5 : False => @lem4083941 A t n h4)). Qed.
Lemma lem4084928 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084927 A t n h1 h2 h3 h4) (@lem4083941 A t n h4)). Qed.
Lemma lem4084929 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (term165 A t s) = False.
Proof. exact (prop_ext (fun h5 : term165 A t s => @lem4084924 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084119 A t s h3)). Qed.
Lemma lem4084930 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084929 A t s h1 h2 h3 h4) (@lem4084119 A t s h3)). Qed.
Lemma lem4084931 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4084930 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084038 A s h2)). Qed.
Lemma lem4084932 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084931 A t s h1 h2 h3 h4) (@lem4084038 A s h2)). Qed.
Lemma lem4084933 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : (@SUBSET A t s) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A t s => @lem4084932 A t s h1 h2 h3 h4) (fun h5 : False => @lem4084030 A t s h4)). Qed.
Lemma lem4084934 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : @FINITE A s) (h3 : term165 A t s) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084933 A t s h1 h2 h3 h4) (@lem4084030 A t s h4)). Qed.
Lemma lem4084935 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (term164 A n t) = False.
Proof. exact (prop_ext (fun h5 : term164 A n t => @lem4084928 A t n h1 h2 h3 h4) (fun h5 : False => @lem4084026 A n t h3)). Qed.
Lemma lem4084936 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084935 A t n h1 h2 h3 h4) (@lem4084026 A n t h3)). Qed.
Lemma lem4084937 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : term81 = False.
Proof. exact (prop_ext (fun h5 : term81 => @lem4084936 A t n h1 h2 h3 h4) (fun h5 : False => @lem4083952 h2)). Qed.
Lemma lem4084938 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084937 A t n h1 h2 h3 h4) (@lem4083952 h2)). Qed.
Lemma lem4084939 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : (@HAS_SIZE A t n) = False.
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A t n => @lem4084938 A t n h1 h2 h3 h4) (fun h5 : False => @lem4083941 A t n h4)). Qed.
Lemma lem4084940 {A : Type'} (t : A -> Prop) (n : nat) (h1 : term36 A) (h2 : term81) (h3 : term164 A n t) (h4 : @HAS_SIZE A t n) : False.
Proof. exact (EQ_MP (@lem4084939 A t n h1 h2 h3 h4) (@lem4083941 A t n h4)). Qed.
Lemma lem4084941 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (or_elim (@lem4083822 A n t s h5) (fun h0 : term164 A n t => @lem4084940 A t n h2 h3 h0 h6) (fun h0 : term165 A t s => @lem4084934 A t s h1 h4 h0 h7)). Qed.
Lemma lem4084942 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : term81 = False.
Proof. exact (prop_ext (fun h8 : term81 => @lem4084941 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083831 h3)). Qed.
Lemma lem4084943 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084942 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083831 h3)). Qed.
Lemma lem4084944 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE A s => @lem4084943 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083798 A s h4)). Qed.
Lemma lem4084945 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084944 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083798 A s h4)). Qed.
Lemma lem4084946 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@HAS_SIZE A t n) = False.
Proof. exact (prop_ext (fun h8 : @HAS_SIZE A t n => @lem4084945 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083794 A t n h6)). Qed.
Lemma lem4084947 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084946 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083794 A t n h6)). Qed.
Lemma lem4084948 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@SUBSET A t s) = False.
Proof. exact (prop_ext (fun h8 : @SUBSET A t s => @lem4084947 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083788 A t s h7)). Qed.
Lemma lem4084949 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084948 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083788 A t s h7)). Qed.
Lemma lem4084950 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : term81 = False.
Proof. exact (prop_ext (fun h8 : term81 => @lem4084949 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083409 h3)). Qed.
Lemma lem4084951 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084950 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083409 h3)). Qed.
Lemma lem4084952 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h8 : @FINITE A s => @lem4084951 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083384 A s h4)). Qed.
Lemma lem4084953 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084952 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083384 A s h4)). Qed.
Lemma lem4084954 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@HAS_SIZE A t n) = False.
Proof. exact (prop_ext (fun h8 : @HAS_SIZE A t n => @lem4084953 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083378 A t n h6)). Qed.
Lemma lem4084955 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084954 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083378 A t n h6)). Qed.
Lemma lem4084956 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : (@SUBSET A t s) = False.
Proof. exact (prop_ext (fun h8 : @SUBSET A t s => @lem4084955 A n t s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4083372 A t s h7)). Qed.
Lemma lem4084957 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term35 A) (h2 : term36 A) (h3 : term81) (h4 : @FINITE A s) (h5 : term34 A n t s) (h6 : @HAS_SIZE A t n) (h7 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4084956 A n t s h1 h2 h3 h4 h5 h6 h7) (@lem4083372 A t s h7)). Qed.
Lemma lem4084958 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term36 A) (h2 : term81) (h3 : @FINITE A s) (h4 : term34 A n t s) (h5 : @HAS_SIZE A t n) (h6 : @SUBSET A t s) : term41 A.
Proof. exact (fun h0 : term35 A => @lem4084957 A n t s h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem4084959 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (@lem69 (term35 A)). Qed.
Lemma lem4084960 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term36 A) (h2 : term81) (h3 : @FINITE A s) (h4 : term34 A n t s) (h5 : @HAS_SIZE A t n) (h6 : @SUBSET A t s) : term42 A.
Proof. exact (EQ_MP (@lem4084959 A) (@lem4084958 A n t s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4084961 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term81) (h2 : @FINITE A s) (h3 : term34 A n t s) (h4 : @HAS_SIZE A t n) (h5 : @SUBSET A t s) : term45 A.
Proof. exact (fun h0 : term36 A => @lem4084960 A n t s h0 h1 h2 h3 h4 h5). Qed.
Lemma lem4084962 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term48 A.
Proof. exact (fun h0 : term81 => @lem4084961 A n t s h0 h1 h2 h3 h4). Qed.
Lemma lem4084963 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term51 A n t s.
Proof. exact (fun h0 : term34 A n t s => @lem4084962 A n t s h1 h0 h2 h3). Qed.
Lemma lem4084964 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : term54 A n t s.
Proof. exact (fun h0 : @FINITE A s => @lem4084963 A n t s h0 h1 h2). Qed.
Lemma lem4084965 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : term57 A n t s.
Proof. exact (fun h0 : @HAS_SIZE A t n => @lem4084964 A n t s h0 h1). Qed.
Lemma lem4084966 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term59 A n t s.
Proof. exact (fun h0 : @SUBSET A t s => @lem4084965 A n t s h0). Qed.
Lemma lem4084971 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term63 A t s.
Proof. exact (fun n : nat => @lem4084966 A n t s). Qed.
Lemma lem4084976 {A : Type'} (s : A -> Prop) : term67 A s.
Proof. exact (fun t : A -> Prop => @lem4084971 A t s). Qed.
Lemma lem4084981 {A : Type'} : term71 A.
Proof. exact (fun s : A -> Prop => @lem4084976 A s). Qed.
Lemma lem4084982 {A : Type'} : term70 A.
Proof. exact (EQ_MP (@lem4083359 A) (@lem4084981 A)). Qed.
Lemma lem4084983 {A : Type'} (s : A -> Prop) : term264 A s.
Proof. exact (@lem4084982 A s). Qed.
Lemma lem4084984 {A : Type'} (s : A -> Prop) : (term264 A s) = (term66 A s).
Proof. exact (eq_refl (term264 A s)). Qed.
Lemma lem4084985 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (EQ_MP (@lem4084984 A s) (@lem4084983 A s)). Qed.
Lemma lem4084986 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term265 A s t.
Proof. exact (@lem4084985 A s t). Qed.
Lemma lem4084987 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term265 A s t) = (term62 A t s).
Proof. exact (eq_refl (term265 A s t)). Qed.
Lemma lem4084988 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term62 A t s.
Proof. exact (EQ_MP (@lem4084987 A t s) (@lem4084986 A s t)). Qed.
Lemma lem4084989 {A : Type'} (t : A -> Prop) (s : A -> Prop) (n : nat) : term266 A t s n.
Proof. exact (@lem4084988 A t s n). Qed.
Lemma lem4084990 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : (term266 A t s n) = (term37 A n t s).
Proof. exact (eq_refl (term266 A t s n)). Qed.
Lemma lem4084991 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term37 A n t s.
Proof. exact (EQ_MP (@lem4084990 A n t s) (@lem4084989 A t s n)). Qed.
Lemma lem4084993 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) : term37 A n t s.
Proof. exact (@lem4083110 A n t s (@lem4084991 A n t s)). Qed.
Lemma lem4084994 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : term56 A n t s.
Proof. exact (@lem4084993 A n t s (@lem4083051 A t s h1)). Qed.
Lemma lem4084995 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : term53 A n t s.
Proof. exact (@lem4084994 A n t s h2 (@lem4083050 A t n h1)). Qed.
Lemma lem4084996 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term50 A n t s.
Proof. exact (@lem4084995 A n t s h2 h3 (@lem4083052 A s h1)). Qed.
Lemma lem4084997 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term47 A.
Proof. exact (@lem4084996 A n t s h1 h3 h4 (@lem4083088 A n t s h2)). Qed.
Lemma lem4084998 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term44 A.
Proof. exact (@lem4084997 A n t s h1 h2 h3 h4 (@lem91603)). Qed.
Lemma lem4084999 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term41 A.
Proof. exact (@lem4084998 A n t s h1 h2 h3 h4 (@lem4083092 A)). Qed.
Lemma lem4085000 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : False.
Proof. exact (@lem4084999 A n t s h1 h2 h3 h4 (@lem4083089 A)). Qed.
Lemma lem4085001 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (term34 A n t s) = False.
Proof. exact (prop_ext (fun h5 : term34 A n t s => @lem4085000 A n t s h1 h2 h3 h4) (fun h5 : False => @lem4083088 A n t s h2)). Qed.
Lemma lem4085002 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A n t s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : False.
Proof. exact (EQ_MP (@lem4085001 A n t s h1 h2 h3 h4) (@lem4083088 A n t s h2)). Qed.
Lemma lem4085003 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term33 A n t s.
Proof. exact (fun h0 : term34 A n t s => @lem4085002 A n t s h1 h0 h2 h3). Qed.
Lemma lem4085004 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term32 A n t s.
Proof. exact (EQ_MP (@lem4083087 A n t s) (@lem4085003 A n t s h1 h2 h3)). Qed.
Lemma lem4085005 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term267 A n s.
Proof. exact (ex_intro (term268 A n s) (@CARD A t) (@lem4085004 A n t s h1 h2 h3)). Qed.
Lemma lem4085006 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @HAS_SIZE A t n) (h3 : @SUBSET A t s) : term83 A n s.
Proof. exact (@lem4083083 A n s (@lem4085005 A n t s h1 h2 h3)). Qed.
Lemma lem4085007 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : term269 A n s.
Proof. exact (fun h0 : @FINITE A s => @lem4085006 A n t s h0 h1 h2). Qed.
Lemma lem4085008 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term12 A s t n) : @HAS_SIZE A t n.
Proof. exact (proj2 (@lem4083049 A s t n h1)). Qed.
Lemma lem4085009 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term12 A s t n) : @SUBSET A t s.
Proof. exact (proj1 (@lem4083049 A s t n h1)). Qed.
Lemma lem4085010 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : (@HAS_SIZE A t n) = (term269 A n s).
Proof. exact (prop_ext (fun h3 : @HAS_SIZE A t n => @lem4085007 A n t s h1 h2) (fun h3 : term269 A n s => @lem4083050 A t n h1)). Qed.
Lemma lem4085011 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : term269 A n s.
Proof. exact (EQ_MP (@lem4085010 A n t s h1 h2) (@lem4083050 A t n h1)). Qed.
Lemma lem4085012 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : (@SUBSET A t s) = (term269 A n s).
Proof. exact (prop_ext (fun h3 : @SUBSET A t s => @lem4085011 A n t s h1 h2) (fun h3 : term269 A n s => @lem4083051 A t s h2)). Qed.
Lemma lem4085013 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : @SUBSET A t s) : term269 A n s.
Proof. exact (EQ_MP (@lem4085012 A n t s h1 h2) (@lem4083051 A t s h2)). Qed.
Lemma lem4085014 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term12 A s t n) (h2 : @SUBSET A t s) : (@HAS_SIZE A t n) = (term269 A n s).
Proof. exact (prop_ext (fun h3 : @HAS_SIZE A t n => @lem4085013 A n t s h3 h2) (fun h3 : term269 A n s => @lem4085008 A s t n h1)). Qed.
Lemma lem4085015 {A : Type'} (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term12 A s t n) (h2 : @SUBSET A t s) : term269 A n s.
Proof. exact (EQ_MP (@lem4085014 A n t s h1 h2) (@lem4085008 A s t n h1)). Qed.
Lemma lem4085016 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term12 A s t n) : (@SUBSET A t s) = (term269 A n s).
Proof. exact (prop_ext (fun h2 : @SUBSET A t s => @lem4085015 A n t s h1 h2) (fun h2 : term269 A n s => @lem4085009 A s t n h1)). Qed.
Lemma lem4085017 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term12 A s t n) : term269 A n s.
Proof. exact (EQ_MP (@lem4085016 A s t n h1) (@lem4085009 A s t n h1)). Qed.
Lemma lem4085018 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term11 A s n) : term269 A n s.
Proof. exact (ex_elim (@lem4083048 A s n h1) (fun t : A -> Prop => fun h0 : term270 A s n t => @lem4085017 A s t n h0)). Qed.
Lemma lem4085020 {A : Type'} (n : nat) (s : A -> Prop) : term271 A n s.
Proof. exact (fun h0 : term11 A s n => @lem4085018 A s n h0). Qed.
Lemma lem4085021 {A : Type'} (n : nat) (s : A -> Prop) : term272 A n s.
Proof. exact (conj (@lem4083035 A s n) (@lem4085020 A n s)). Qed.
Lemma lem4085022 {A : Type'} (s : A -> Prop) (n : nat) : (term272 A n s) = ((term269 A n s) = (term11 A s n)).
Proof. exact (@lem32 (term269 A n s) (term11 A s n)). Qed.
Lemma lem4085023 {A : Type'} (s : A -> Prop) (n : nat) : (term269 A n s) = (term11 A s n).
Proof. exact (EQ_MP (@lem4085022 A s n) (@lem4085021 A n s)). Qed.
Lemma lem4085028 {A : Type'} (n : nat) : term273 A n.
Proof. exact (fun s : A -> Prop => @lem4085023 A s n). Qed.
Lemma lem4085033 {A : Type'} : term274 A.
Proof. exact (fun n : nat => @lem4085028 A n). Qed.
