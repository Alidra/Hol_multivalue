Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ADD_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import SUM_ADD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem7210022 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7210023 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7210024 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7210023 m) (@lem7210022 m)). Qed.
Lemma lem7210025 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7210024 m n). Qed.
Lemma lem7210026 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7210027 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7210026 m n) (@lem7210025 m n)). Qed.
Lemma lem7210028 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7210030 {_131713 : Type'} (f : _131713 -> real) : term4 _131713 f.
Proof. exact (@lem7068796 _131713 f). Qed.
Lemma lem7210031 {_131713 : Type'} (f : _131713 -> real) : (term4 _131713 f) = (term5 _131713 f).
Proof. exact (eq_refl (term4 _131713 f)). Qed.
Lemma lem7210032 {_131713 : Type'} (f : _131713 -> real) : term5 _131713 f.
Proof. exact (EQ_MP (@lem7210031 _131713 f) (@lem7210030 _131713 f)). Qed.
Lemma lem7210033 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term6 _131713 f g.
Proof. exact (@lem7210032 _131713 f g). Qed.
Lemma lem7210034 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term6 _131713 f g) = (term7 _131713 f g).
Proof. exact (eq_refl (term6 _131713 f g)). Qed.
Lemma lem7210035 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term7 _131713 f g.
Proof. exact (EQ_MP (@lem7210034 _131713 f g) (@lem7210033 _131713 f g)). Qed.
Lemma lem7210036 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) : term8 _131713 f g s.
Proof. exact (@lem7210035 _131713 f g s). Qed.
Lemma lem7210037 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : (term8 _131713 f g s) = (term9 _131713 f s g).
Proof. exact (eq_refl (term8 _131713 f g s)). Qed.
Lemma lem7210038 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term9 _131713 f s g.
Proof. exact (EQ_MP (@lem7210037 _131713 f s g) (@lem7210036 _131713 f g s)). Qed.
Lemma lem7210039 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : @FINITE _131713 s.
Proof. exact (h1). Qed.
Lemma lem7210040 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term10 _131713 s f g) = (term11 _131713 f s g).
Proof. exact (@lem7210038 _131713 f s g (@lem7210039 _131713 s h1)). Qed.
Lemma lem7210065 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term9 _131713 f s g.
Proof. exact (fun h0 : @FINITE _131713 s => @lem7210040 _131713 f g s h0). Qed.
Lemma lem7210066 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : term12 f s g.
Proof. exact (@lem7210065 nat f s g). Qed.
Lemma lem7210067 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : term13 f m n g.
Proof. exact (@lem7210066 f (dotdot m n) g). Qed.
Lemma lem7210069 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7210028 m n) (@lem7210027 m n)). Qed.
Lemma lem7210070 (m : nat) (n : nat) : True = (term3 m n).
Proof. exact (SYM (@lem7210069 m n)). Qed.
Lemma lem7210071 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7210070 m n) (@lem0)). Qed.
Lemma lem7210072 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term14 m n f g) = (term15 f m n g).
Proof. exact (@lem7210067 f m n g (@lem7210071 m n)). Qed.
Lemma lem7210073 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7210074 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term16 m n f g) = (term17 f m n g).
Proof. exact (MK_COMB (@lem7210073) (@lem7210072 f m n g)). Qed.
Lemma lem7210075 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term15 f m n g) = (term15 f m n g).
Proof. exact (eq_refl (term15 f m n g)). Qed.
Lemma lem7210076 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term14 m n f g) = (term15 f m n g)) = ((term15 f m n g) = (term15 f m n g)).
Proof. exact (MK_COMB (@lem7210074 f m n g) (@lem7210075 f m n g)). Qed.
Lemma lem7210078 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7210079 (x : real) : (x = x) = True.
Proof. exact (@lem7210078 real x). Qed.
Lemma lem7210080 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term15 f m n g) = (term15 f m n g)) = True.
Proof. exact (@lem7210079 (term15 f m n g)). Qed.
Lemma lem7210081 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : ((term14 m n f g) = (term15 f m n g)) = True.
Proof. exact (TRANS (@lem7210076 f m n g) (@lem7210080 f m n g)). Qed.
Lemma lem7210082 (f : nat -> real) (m : nat) (g : nat -> real) : (term18 f m g) = term19.
Proof. exact (fun_ext (fun n : nat => @lem7210081 f m n g)). Qed.
Lemma lem7210083 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210084 (f : nat -> real) (m : nat) (g : nat -> real) : (term20 f m g) = term21.
Proof. exact (MK_COMB (@lem7210083) (@lem7210082 f m g)). Qed.
Lemma lem7210086 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210087 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7210086 nat t). Qed.
Lemma lem7210088 : term21 = True.
Proof. exact (@lem7210087 True). Qed.
Lemma lem7210089 (f : nat -> real) (m : nat) (g : nat -> real) : (term20 f m g) = True.
Proof. exact (TRANS (@lem7210084 f m g) (@lem7210088)). Qed.
Lemma lem7210090 (f : nat -> real) (g : nat -> real) : (term24 f g) = term19.
Proof. exact (fun_ext (fun m : nat => @lem7210089 f m g)). Qed.
Lemma lem7210091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7210092 (f : nat -> real) (g : nat -> real) : (term25 f g) = term21.
Proof. exact (MK_COMB (@lem7210091) (@lem7210090 f g)). Qed.
Lemma lem7210094 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210095 (t : Prop) : (term23 t) = t.
Proof. exact (@lem7210094 nat t). Qed.
Lemma lem7210096 : term21 = True.
Proof. exact (@lem7210095 True). Qed.
Lemma lem7210097 (f : nat -> real) (g : nat -> real) : (term25 f g) = True.
Proof. exact (TRANS (@lem7210092 f g) (@lem7210096)). Qed.
Lemma lem7210098 (f : nat -> real) : (term26 f) = term27.
Proof. exact (fun_ext (fun g : nat -> real => @lem7210097 f g)). Qed.
Lemma lem7210099 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210100 (f : nat -> real) : (term28 f) = term29.
Proof. exact (MK_COMB (@lem7210099) (@lem7210098 f)). Qed.
Lemma lem7210102 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210103 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7210102 (nat -> real) t). Qed.
Lemma lem7210104 : term29 = True.
Proof. exact (@lem7210103 True). Qed.
Lemma lem7210105 (f : nat -> real) : (term28 f) = True.
Proof. exact (TRANS (@lem7210100 f) (@lem7210104)). Qed.
Lemma lem7210106 : term31 = term27.
Proof. exact (fun_ext (fun f : nat -> real => @lem7210105 f)). Qed.
Lemma lem7210107 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7210108 : term32 = term29.
Proof. exact (MK_COMB (@lem7210107) (@lem7210106)). Qed.
Lemma lem7210110 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7210111 (t : Prop) : (term30 t) = t.
Proof. exact (@lem7210110 (nat -> real) t). Qed.
Lemma lem7210112 : term29 = True.
Proof. exact (@lem7210111 True). Qed.
Lemma lem7210113 : term32 = True.
Proof. exact (TRANS (@lem7210108) (@lem7210112)). Qed.
Lemma lem7210114 : True = term32.
Proof. exact (SYM (@lem7210113)). Qed.
Lemma lem7210115 : term32.
Proof. exact (EQ_MP (@lem7210114) (@lem0)). Qed.
