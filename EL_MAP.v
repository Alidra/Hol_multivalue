Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_MAP_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1097797_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem1207007 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1207009 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1207010 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term2 _28366 _28367 f.
Proof. exact (@lem1207009 (term3 _28366 _28367 f)). Qed.
Lemma lem1207011 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term4 _28366 _28367 f) = (term5 _28366 _28367 f).
Proof. exact (eq_refl (term4 _28366 _28367 f)). Qed.
Lemma lem1207012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207013 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term6 _28366 _28367 f) = (term7 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207012) (@lem1207011 _28366 _28367 f)). Qed.
Lemma lem1207014 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term8 _28366 _28367 f n) = (term9 _28366 _28367 f n).
Proof. exact (eq_refl (term8 _28366 _28367 f n)). Qed.
Lemma lem1207015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207016 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term10 _28366 _28367 f n) = (term11 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207015) (@lem1207014 _28366 _28367 f n)). Qed.
Lemma lem1207017 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term12 _28366 _28367 f n) = (term13 _28366 _28367 f n).
Proof. exact (eq_refl (term12 _28366 _28367 f n)). Qed.
Lemma lem1207018 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term14 _28366 _28367 f n) = (term15 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207016 _28366 _28367 f n) (@lem1207017 _28366 _28367 f n)). Qed.
Lemma lem1207019 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term16 _28366 _28367 f) = (term17 _28366 _28367 f).
Proof. exact (fun_ext (fun n : nat => @lem1207018 _28366 _28367 f n)). Qed.
Lemma lem1207020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1207021 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term18 _28366 _28367 f) = (term19 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207020) (@lem1207019 _28366 _28367 f)). Qed.
Lemma lem1207022 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term20 _28366 _28367 f) = (term21 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207013 _28366 _28367 f) (@lem1207021 _28366 _28367 f)). Qed.
Lemma lem1207023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207024 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term22 _28366 _28367 f) = (term23 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207023) (@lem1207022 _28366 _28367 f)). Qed.
Lemma lem1207025 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term8 _28366 _28367 f n) = (term9 _28366 _28367 f n).
Proof. exact (eq_refl (term8 _28366 _28367 f n)). Qed.
Lemma lem1207026 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term24 _28366 _28367 f) = (term3 _28366 _28367 f).
Proof. exact (fun_ext (fun n : nat => @lem1207025 _28366 _28367 f n)). Qed.
Lemma lem1207027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1207028 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term25 _28366 _28367 f) = (term26 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207027) (@lem1207026 _28366 _28367 f)). Qed.
Lemma lem1207029 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term2 _28366 _28367 f) = (term27 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207024 _28366 _28367 f) (@lem1207028 _28366 _28367 f)). Qed.
Lemma lem1207030 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term27 _28366 _28367 f.
Proof. exact (EQ_MP (@lem1207029 _28366 _28367 f) (@lem1207010 _28366 _28367 f)). Qed.
Lemma lem1207031 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term9 _28366 _28367 f n.
Proof. exact (h1). Qed.
Lemma lem1207033 {A : Type'} (P : type1143 A) : term28 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1207034 {_28367 : Type'} (P : type1143 _28367) : term28 _28367 P.
Proof. exact (@lem1207033 _28367 P). Qed.
Lemma lem1207035 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term29 _28366 _28367 f.
Proof. exact (@lem1207034 _28367 (term30 _28366 _28367 f)). Qed.
Lemma lem1207036 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term31 _28366 _28367 f) = (term32 _28366 _28367 f).
Proof. exact (eq_refl (term31 _28366 _28367 f)). Qed.
Lemma lem1207037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207038 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term33 _28366 _28367 f) = (term34 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207037) (@lem1207036 _28366 _28367 f)). Qed.
Lemma lem1207039 {_28366 _28367 : Type'} (f : _28367 -> _28366) (t : list _28367) : (term35 _28366 _28367 f t) = (term36 _28366 _28367 f t).
Proof. exact (eq_refl (term35 _28366 _28367 f t)). Qed.
Lemma lem1207040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207041 {_28366 _28367 : Type'} (f : _28367 -> _28366) (t : list _28367) : (term37 _28366 _28367 f t) = (term38 _28366 _28367 f t).
Proof. exact (MK_COMB (@lem1207040) (@lem1207039 _28366 _28367 f t)). Qed.
Lemma lem1207042 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term39 _28366 _28367 f h t) = (term40 _28366 _28367 f h t).
Proof. exact (eq_refl (term39 _28366 _28367 f h t)). Qed.
Lemma lem1207043 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term41 _28366 _28367 f h t) = (term42 _28366 _28367 f h t).
Proof. exact (MK_COMB (@lem1207041 _28366 _28367 f t) (@lem1207042 _28366 _28367 f h t)). Qed.
Lemma lem1207044 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) : (term43 _28366 _28367 f h) = (term44 _28366 _28367 f h).
Proof. exact (fun_ext (fun t : list _28367 => @lem1207043 _28366 _28367 f h t)). Qed.
Lemma lem1207045 {_28367 : Type'} : (@all (list _28367)) = (@all (list _28367)).
Proof. exact (eq_refl (@all (list _28367))). Qed.
Lemma lem1207046 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) : (term45 _28366 _28367 f h) = (term46 _28366 _28367 f h).
Proof. exact (MK_COMB (@lem1207045 _28367) (@lem1207044 _28366 _28367 f h)). Qed.
Lemma lem1207047 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term47 _28366 _28367 f) = (term48 _28366 _28367 f).
Proof. exact (fun_ext (fun h : _28367 => @lem1207046 _28366 _28367 f h)). Qed.
Lemma lem1207048 {_28367 : Type'} : (@all _28367) = (@all _28367).
Proof. exact (eq_refl (@all _28367)). Qed.
Lemma lem1207049 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term49 _28366 _28367 f) = (term50 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207048 _28367) (@lem1207047 _28366 _28367 f)). Qed.
Lemma lem1207050 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term51 _28366 _28367 f) = (term52 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207038 _28366 _28367 f) (@lem1207049 _28366 _28367 f)). Qed.
Lemma lem1207051 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207052 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term53 _28366 _28367 f) = (term54 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207051) (@lem1207050 _28366 _28367 f)). Qed.
Lemma lem1207053 {_28366 _28367 : Type'} (f : _28367 -> _28366) (l : list _28367) : (term35 _28366 _28367 f l) = (term36 _28366 _28367 f l).
Proof. exact (eq_refl (term35 _28366 _28367 f l)). Qed.
Lemma lem1207054 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term55 _28366 _28367 f) = (term30 _28366 _28367 f).
Proof. exact (fun_ext (fun l : list _28367 => @lem1207053 _28366 _28367 f l)). Qed.
Lemma lem1207055 {_28367 : Type'} : (@all (list _28367)) = (@all (list _28367)).
Proof. exact (eq_refl (@all (list _28367))). Qed.
Lemma lem1207056 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term56 _28366 _28367 f) = (term5 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207055 _28367) (@lem1207054 _28366 _28367 f)). Qed.
Lemma lem1207057 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term29 _28366 _28367 f) = (term57 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207052 _28366 _28367 f) (@lem1207056 _28366 _28367 f)). Qed.
Lemma lem1207058 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term57 _28366 _28367 f.
Proof. exact (EQ_MP (@lem1207057 _28366 _28367 f) (@lem1207035 _28366 _28367 f)). Qed.
Lemma lem1207061 {A : Type'} (P : type1143 A) : term28 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1207062 {_28367 : Type'} (P : type1143 _28367) : term28 _28367 P.
Proof. exact (@lem1207061 _28367 P). Qed.
Lemma lem1207063 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : term58 _28366 _28367 f n.
Proof. exact (@lem1207062 _28367 (term59 _28366 _28367 f n)). Qed.
Lemma lem1207064 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term60 _28366 _28367 f n) = (term61 _28366 _28367 f n).
Proof. exact (eq_refl (term60 _28366 _28367 f n)). Qed.
Lemma lem1207065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207066 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term62 _28366 _28367 f n) = (term63 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207065) (@lem1207064 _28366 _28367 f n)). Qed.
Lemma lem1207067 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (t : list _28367) : (term64 _28366 _28367 f n t) = (term65 _28366 _28367 f n t).
Proof. exact (eq_refl (term64 _28366 _28367 f n t)). Qed.
Lemma lem1207068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207069 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (t : list _28367) : (term66 _28366 _28367 f n t) = (term67 _28366 _28367 f n t).
Proof. exact (MK_COMB (@lem1207068) (@lem1207067 _28366 _28367 f n t)). Qed.
Lemma lem1207070 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h : _28367) (t : list _28367) : (term68 _28366 _28367 f n h t) = (term69 _28366 _28367 f n h t).
Proof. exact (eq_refl (term68 _28366 _28367 f n h t)). Qed.
Lemma lem1207071 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h : _28367) (t : list _28367) : (term70 _28366 _28367 f n h t) = (term71 _28366 _28367 f n h t).
Proof. exact (MK_COMB (@lem1207069 _28366 _28367 f n t) (@lem1207070 _28366 _28367 f n h t)). Qed.
Lemma lem1207072 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h : _28367) : (term72 _28366 _28367 f n h) = (term73 _28366 _28367 f n h).
Proof. exact (fun_ext (fun t : list _28367 => @lem1207071 _28366 _28367 f n h t)). Qed.
Lemma lem1207073 {_28367 : Type'} : (@all (list _28367)) = (@all (list _28367)).
Proof. exact (eq_refl (@all (list _28367))). Qed.
Lemma lem1207074 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h : _28367) : (term74 _28366 _28367 f n h) = (term75 _28366 _28367 f n h).
Proof. exact (MK_COMB (@lem1207073 _28367) (@lem1207072 _28366 _28367 f n h)). Qed.
Lemma lem1207075 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term76 _28366 _28367 f n) = (term77 _28366 _28367 f n).
Proof. exact (fun_ext (fun h : _28367 => @lem1207074 _28366 _28367 f n h)). Qed.
Lemma lem1207076 {_28367 : Type'} : (@all _28367) = (@all _28367).
Proof. exact (eq_refl (@all _28367)). Qed.
Lemma lem1207077 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term78 _28366 _28367 f n) = (term79 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207076 _28367) (@lem1207075 _28366 _28367 f n)). Qed.
Lemma lem1207078 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term80 _28366 _28367 f n) = (term81 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207066 _28366 _28367 f n) (@lem1207077 _28366 _28367 f n)). Qed.
Lemma lem1207079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207080 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term82 _28366 _28367 f n) = (term83 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207079) (@lem1207078 _28366 _28367 f n)). Qed.
Lemma lem1207081 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (l : list _28367) : (term64 _28366 _28367 f n l) = (term65 _28366 _28367 f n l).
Proof. exact (eq_refl (term64 _28366 _28367 f n l)). Qed.
Lemma lem1207082 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term84 _28366 _28367 f n) = (term59 _28366 _28367 f n).
Proof. exact (fun_ext (fun l : list _28367 => @lem1207081 _28366 _28367 f n l)). Qed.
Lemma lem1207083 {_28367 : Type'} : (@all (list _28367)) = (@all (list _28367)).
Proof. exact (eq_refl (@all (list _28367))). Qed.
Lemma lem1207084 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term85 _28366 _28367 f n) = (term13 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207083 _28367) (@lem1207082 _28366 _28367 f n)). Qed.
Lemma lem1207085 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term58 _28366 _28367 f n) = (term86 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207080 _28366 _28367 f n) (@lem1207084 _28366 _28367 f n)). Qed.
Lemma lem1207086 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : term86 _28366 _28367 f n.
Proof. exact (EQ_MP (@lem1207085 _28366 _28367 f n) (@lem1207063 _28366 _28367 f n)). Qed.
Lemma lem1207104 {A B : Type'} : term87 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1207105 {A B : Type'} (f : A -> B) : term88 A B f.
Proof. exact (@lem1207104 A B f). Qed.
Lemma lem1207106 {A B : Type'} (f : A -> B) : (term88 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term88 A B f)). Qed.
Lemma lem1207115 (m : nat) : term89 m.
Proof. exact (@lem1207007 m). Qed.
Lemma lem1207116 (m : nat) : (term89 m) = ((term90 m) = False).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1207129 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1207130 {_28367 : Type'} : (@List.length _28367 (@nil _28367)) = (NUMERAL 0).
Proof. exact (@lem1207129 _28367). Qed.
Lemma lem1207131 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem1207132 {_28367 : Type'} : (term92 _28367) = term93.
Proof. exact (MK_COMB (@lem1207131) (@lem1207130 _28367)). Qed.
Lemma lem1207134 (m : nat) : (term90 m) = False.
Proof. exact (EQ_MP (@lem1207116 m) (@lem1207115 m)). Qed.
Lemma lem1207135 : term93 = False.
Proof. exact (@lem1207134 (NUMERAL 0)). Qed.
Lemma lem1207136 {_28367 : Type'} : (term92 _28367) = False.
Proof. exact (TRANS (@lem1207132 _28367) (@lem1207135)). Qed.
Lemma lem1207137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207138 {_28367 : Type'} : (term94 _28367) = (imp False).
Proof. exact (MK_COMB (@lem1207137) (@lem1207136 _28367)). Qed.
Lemma lem1207142 {_25569 : Type'} (l : list _25569) : (term95 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1207143 {_28366 : Type'} (l : list _28366) : (term95 _28366 l) = (@hd _28366 l).
Proof. exact (@lem1207142 _28366 l). Qed.
Lemma lem1207144 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term96 _28366 _28367 f) = (term97 _28366 _28367 f).
Proof. exact (@lem1207143 _28366 (@List.map _28367 _28366 f (@nil _28367))). Qed.
Lemma lem1207146 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1207106 A B f) (@lem1207105 A B f)). Qed.
Lemma lem1207147 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (@List.map _28367 _28366 f (@nil _28367)) = (@nil _28366).
Proof. exact (@lem1207146 _28367 _28366 f). Qed.
Lemma lem1207148 {_28366 : Type'} : (@hd _28366) = (@hd _28366).
Proof. exact (eq_refl (@hd _28366)). Qed.
Lemma lem1207149 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term97 _28366 _28367 f) = (@hd _28366 (@nil _28366)).
Proof. exact (MK_COMB (@lem1207148 _28366) (@lem1207147 _28366 _28367 f)). Qed.
Lemma lem1207150 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term96 _28366 _28367 f) = (@hd _28366 (@nil _28366)).
Proof. exact (TRANS (@lem1207144 _28366 _28367 f) (@lem1207149 _28366 _28367 f)). Qed.
Lemma lem1207151 {_28366 : Type'} : (@eq _28366) = (@eq _28366).
Proof. exact (eq_refl (@eq _28366)). Qed.
Lemma lem1207152 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term98 _28366 _28367 f) = (term99 _28366).
Proof. exact (MK_COMB (@lem1207151 _28366) (@lem1207150 _28366 _28367 f)). Qed.
Lemma lem1207154 {_25569 : Type'} (l : list _25569) : (term95 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1207155 {_28367 : Type'} (l : list _28367) : (term95 _28367 l) = (@hd _28367 l).
Proof. exact (@lem1207154 _28367 l). Qed.
Lemma lem1207156 {_28367 : Type'} : (term100 _28367) = (@hd _28367 (@nil _28367)).
Proof. exact (@lem1207155 _28367 (@nil _28367)). Qed.
Lemma lem1207157 {_28366 _28367 : Type'} (f : _28367 -> _28366) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1207158 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term101 _28366 _28367 f) = (term102 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207157 _28366 _28367 f) (@lem1207156 _28367)). Qed.
Lemma lem1207159 {_28366 _28367 : Type'} (f : _28367 -> _28366) : ((term96 _28366 _28367 f) = (term101 _28366 _28367 f)) = ((@hd _28366 (@nil _28366)) = (term102 _28366 _28367 f)).
Proof. exact (MK_COMB (@lem1207152 _28366 _28367 f) (@lem1207158 _28366 _28367 f)). Qed.
Lemma lem1207162 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term32 _28366 _28367 f) = (term103 _28366 _28367 f).
Proof. exact (MK_COMB (@lem1207138 _28367) (@lem1207159 _28366 _28367 f)). Qed.
Lemma lem1207164 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1207165 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term103 _28366 _28367 f) = True.
Proof. exact (@lem1207164 ((@hd _28366 (@nil _28366)) = (term102 _28366 _28367 f))). Qed.
Lemma lem1207166 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term32 _28366 _28367 f) = True.
Proof. exact (TRANS (@lem1207162 _28366 _28367 f) (@lem1207165 _28366 _28367 f)). Qed.
Lemma lem1207167 {_28366 _28367 : Type'} (f : _28367 -> _28366) : True = (term32 _28366 _28367 f).
Proof. exact (SYM (@lem1207166 _28366 _28367 f)). Qed.
Lemma lem1207168 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term32 _28366 _28367 f.
Proof. exact (EQ_MP (@lem1207167 _28366 _28367 f) (@lem0)). Qed.
Lemma lem1207175 {A B : Type'} : term104 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1207176 {A B : Type'} (f : A -> B) : term105 A B f.
Proof. exact (@lem1207175 A B f). Qed.
Lemma lem1207177 {A B : Type'} (f : A -> B) : (term105 A B f) = (term106 A B f).
Proof. exact (eq_refl (term105 A B f)). Qed.
Lemma lem1207178 {A B : Type'} (f : A -> B) : term106 A B f.
Proof. exact (EQ_MP (@lem1207177 A B f) (@lem1207176 A B f)). Qed.
Lemma lem1207179 {A B : Type'} (f : A -> B) (h : A) : term107 A B f h.
Proof. exact (@lem1207178 A B f h). Qed.
Lemma lem1207180 {A B : Type'} (h : A) (f : A -> B) : (term107 A B f h) = (term108 A B h f).
Proof. exact (eq_refl (term107 A B f h)). Qed.
Lemma lem1207181 {A B : Type'} (h : A) (f : A -> B) : term108 A B h f.
Proof. exact (EQ_MP (@lem1207180 A B h f) (@lem1207179 A B f h)). Qed.
Lemma lem1207182 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term109 A B h f t.
Proof. exact (@lem1207181 A B h f t). Qed.
Lemma lem1207183 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term109 A B h f t) = ((term110 A B f h t) = (term111 A B h f t)).
Proof. exact (eq_refl (term109 A B h f t)). Qed.
Lemma lem1207191 (n : nat) : term112 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem1207192 (n : nat) : (term112 n) = (term113 n).
Proof. exact (eq_refl (term112 n)). Qed.
Lemma lem1207193 (n : nat) : term113 n.
Proof. exact (EQ_MP (@lem1207192 n) (@lem1207191 n)). Qed.
Lemma lem1207194 (n : nat) : (term113 n) = ((term113 n) = True).
Proof. exact (@lem7 (term113 n)). Qed.
Lemma lem1207199 {A : Type'} : term114 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1207200 {A : Type'} (h : A) : term115 A h.
Proof. exact (@lem1207199 A h). Qed.
Lemma lem1207201 {A : Type'} (h : A) : (term115 A h) = (term116 A h).
Proof. exact (eq_refl (term115 A h)). Qed.
Lemma lem1207202 {A : Type'} (h : A) : term116 A h.
Proof. exact (EQ_MP (@lem1207201 A h) (@lem1207200 A h)). Qed.
Lemma lem1207203 {A : Type'} (h : A) (t : list A) : term117 A h t.
Proof. exact (@lem1207202 A h t). Qed.
Lemma lem1207204 {A : Type'} (h : A) (t : list A) : (term117 A h t) = ((term118 A h t) = (term119 A t)).
Proof. exact (eq_refl (term117 A h t)). Qed.
Lemma lem1207212 {A : Type'} (h : A) (t : list A) : (term118 A h t) = (term119 A t).
Proof. exact (EQ_MP (@lem1207204 A h t) (@lem1207203 A h t)). Qed.
Lemma lem1207213 {_28367 : Type'} (h : _28367) (t : list _28367) : (term118 _28367 h t) = (term119 _28367 t).
Proof. exact (@lem1207212 _28367 h t). Qed.
Lemma lem1207214 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem1207215 {_28367 : Type'} (h : _28367) (t : list _28367) : (term120 _28367 h t) = (term121 _28367 t).
Proof. exact (MK_COMB (@lem1207214) (@lem1207213 _28367 h t)). Qed.
Lemma lem1207217 (n : nat) : (term113 n) = True.
Proof. exact (EQ_MP (@lem1207194 n) (@lem1207193 n)). Qed.
Lemma lem1207218 {_28367 : Type'} (t : list _28367) : (term121 _28367 t) = True.
Proof. exact (@lem1207217 (@List.length _28367 t)). Qed.
Lemma lem1207219 {_28367 : Type'} (h : _28367) (t : list _28367) : (term120 _28367 h t) = True.
Proof. exact (TRANS (@lem1207215 _28367 h t) (@lem1207218 _28367 t)). Qed.
Lemma lem1207220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207221 {_28367 : Type'} (h : _28367) (t : list _28367) : (term122 _28367 h t) = (imp True).
Proof. exact (MK_COMB (@lem1207220) (@lem1207219 _28367 h t)). Qed.
Lemma lem1207225 {_25569 : Type'} (l : list _25569) : (term95 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1207226 {_28366 : Type'} (l : list _28366) : (term95 _28366 l) = (@hd _28366 l).
Proof. exact (@lem1207225 _28366 l). Qed.
Lemma lem1207227 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term123 _28366 _28367 f h t) = (term124 _28366 _28367 f h t).
Proof. exact (@lem1207226 _28366 (term125 _28366 _28367 f h t)). Qed.
Lemma lem1207229 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term110 A B f h t) = (term111 A B h f t).
Proof. exact (EQ_MP (@lem1207183 A B h f t) (@lem1207182 A B h f t)). Qed.
Lemma lem1207230 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term125 _28366 _28367 f h t) = (term126 _28366 _28367 h f t).
Proof. exact (@lem1207229 _28367 _28366 h f t). Qed.
Lemma lem1207231 {_28366 : Type'} : (@hd _28366) = (@hd _28366).
Proof. exact (eq_refl (@hd _28366)). Qed.
Lemma lem1207232 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term124 _28366 _28367 f h t) = (term127 _28366 _28367 h f t).
Proof. exact (MK_COMB (@lem1207231 _28366) (@lem1207230 _28366 _28367 h f t)). Qed.
Lemma lem1207234 {A : Type'} (t : list A) (h : A) : (term128 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1207235 {_28366 : Type'} (t : list _28366) (h : _28366) : (term128 _28366 h t) = h.
Proof. exact (@lem1207234 _28366 t h). Qed.
Lemma lem1207236 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : (term127 _28366 _28367 h f t) = (f h).
Proof. exact (@lem1207235 _28366 (@List.map _28367 _28366 f t) (f h)). Qed.
Lemma lem1207237 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : (term124 _28366 _28367 f h t) = (f h).
Proof. exact (TRANS (@lem1207232 _28366 _28367 h f t) (@lem1207236 _28366 _28367 t f h)). Qed.
Lemma lem1207238 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : (term123 _28366 _28367 f h t) = (f h).
Proof. exact (TRANS (@lem1207227 _28366 _28367 f h t) (@lem1207237 _28366 _28367 t f h)). Qed.
Lemma lem1207239 {_28366 : Type'} : (@eq _28366) = (@eq _28366).
Proof. exact (eq_refl (@eq _28366)). Qed.
Lemma lem1207240 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : (term129 _28366 _28367 f h t) = (term130 _28366 _28367 f h).
Proof. exact (MK_COMB (@lem1207239 _28366) (@lem1207238 _28366 _28367 t f h)). Qed.
Lemma lem1207242 {_25569 : Type'} (l : list _25569) : (term95 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1207243 {_28367 : Type'} (l : list _28367) : (term95 _28367 l) = (@hd _28367 l).
Proof. exact (@lem1207242 _28367 l). Qed.
Lemma lem1207244 {_28367 : Type'} (h : _28367) (t : list _28367) : (term131 _28367 h t) = (term128 _28367 h t).
Proof. exact (@lem1207243 _28367 (@cons _28367 h t)). Qed.
Lemma lem1207246 {A : Type'} (t : list A) (h : A) : (term128 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1207247 {_28367 : Type'} (t : list _28367) (h : _28367) : (term128 _28367 h t) = h.
Proof. exact (@lem1207246 _28367 t h). Qed.
Lemma lem1207248 {_28367 : Type'} (t : list _28367) (h : _28367) : (term131 _28367 h t) = h.
Proof. exact (TRANS (@lem1207244 _28367 h t) (@lem1207247 _28367 t h)). Qed.
Lemma lem1207249 {_28366 _28367 : Type'} (f : _28367 -> _28366) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1207250 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : (term132 _28366 _28367 f h t) = (f h).
Proof. exact (MK_COMB (@lem1207249 _28366 _28367 f) (@lem1207248 _28367 t h)). Qed.
Lemma lem1207251 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (h : _28367) : ((term123 _28366 _28367 f h t) = (term132 _28366 _28367 f h t)) = ((f h) = (f h)).
Proof. exact (MK_COMB (@lem1207240 _28366 _28367 t f h) (@lem1207250 _28366 _28367 t f h)). Qed.
Lemma lem1207253 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207254 {_28366 : Type'} (x : _28366) : (x = x) = True.
Proof. exact (@lem1207253 _28366 x). Qed.
Lemma lem1207255 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) : ((f h) = (f h)) = True.
Proof. exact (@lem1207254 _28366 (f h)). Qed.
Lemma lem1207256 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : ((term123 _28366 _28367 f h t) = (term132 _28366 _28367 f h t)) = True.
Proof. exact (TRANS (@lem1207251 _28366 _28367 t f h) (@lem1207255 _28366 _28367 f h)). Qed.
Lemma lem1207257 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term40 _28366 _28367 f h t) = (True -> True).
Proof. exact (MK_COMB (@lem1207221 _28367 h t) (@lem1207256 _28366 _28367 f h t)). Qed.
Lemma lem1207259 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1207260 : (True -> True) = True.
Proof. exact (@lem1207259 True). Qed.
Lemma lem1207261 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term40 _28366 _28367 f h t) = True.
Proof. exact (TRANS (@lem1207257 _28366 _28367 f h t) (@lem1207260)). Qed.
Lemma lem1207262 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : True = (term40 _28366 _28367 f h t).
Proof. exact (SYM (@lem1207261 _28366 _28367 f h t)). Qed.
Lemma lem1207263 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : term40 _28366 _28367 f h t.
Proof. exact (EQ_MP (@lem1207262 _28366 _28367 f h t) (@lem0)). Qed.
Lemma lem1207280 {A B : Type'} : term87 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1207281 {A B : Type'} (f : A -> B) : term88 A B f.
Proof. exact (@lem1207280 A B f). Qed.
Lemma lem1207282 {A B : Type'} (f : A -> B) : (term88 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term88 A B f)). Qed.
Lemma lem1207291 (m : nat) : term89 m.
Proof. exact (@lem1207007 m). Qed.
Lemma lem1207292 (m : nat) : (term89 m) = ((term90 m) = False).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem1207310 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1207311 {_28367 : Type'} : (@List.length _28367 (@nil _28367)) = (NUMERAL 0).
Proof. exact (@lem1207310 _28367). Qed.
Lemma lem1207312 (n : nat) : (term133 n) = (term133 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem1207313 {_28367 : Type'} (n : nat) : (term134 _28367 n) = (term135 n).
Proof. exact (MK_COMB (@lem1207312 n) (@lem1207311 _28367)). Qed.
Lemma lem1207315 (m : nat) : (term90 m) = False.
Proof. exact (EQ_MP (@lem1207292 m) (@lem1207291 m)). Qed.
Lemma lem1207316 (n : nat) : (term135 n) = False.
Proof. exact (@lem1207315 (S n)). Qed.
Lemma lem1207317 {_28367 : Type'} (n : nat) : (term134 _28367 n) = False.
Proof. exact (TRANS (@lem1207313 _28367 n) (@lem1207316 n)). Qed.
Lemma lem1207318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207319 {_28367 : Type'} (n : nat) : (term136 _28367 n) = (imp False).
Proof. exact (MK_COMB (@lem1207318) (@lem1207317 _28367 n)). Qed.
Lemma lem1207323 {_25569 : Type'} (n : nat) (l : list _25569) : (term137 _25569 n l) = (term138 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1207324 {_28366 : Type'} (n : nat) (l : list _28366) : (term137 _28366 n l) = (term138 _28366 n l).
Proof. exact (@lem1207323 _28366 n l). Qed.
Lemma lem1207325 {_28366 _28367 : Type'} (n : nat) (f : _28367 -> _28366) : (term139 _28366 _28367 n f) = (term140 _28366 _28367 n f).
Proof. exact (@lem1207324 _28366 n (@List.map _28367 _28366 f (@nil _28367))). Qed.
Lemma lem1207327 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1207282 A B f) (@lem1207281 A B f)). Qed.
Lemma lem1207328 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (@List.map _28367 _28366 f (@nil _28367)) = (@nil _28366).
Proof. exact (@lem1207327 _28367 _28366 f). Qed.
Lemma lem1207329 {_28366 : Type'} : (@tl _28366) = (@tl _28366).
Proof. exact (eq_refl (@tl _28366)). Qed.
Lemma lem1207330 {_28366 _28367 : Type'} (f : _28367 -> _28366) : (term141 _28366 _28367 f) = (@tl _28366 (@nil _28366)).
Proof. exact (MK_COMB (@lem1207329 _28366) (@lem1207328 _28366 _28367 f)). Qed.
Lemma lem1207331 {_28366 : Type'} (n : nat) : (@EL _28366 n) = (@EL _28366 n).
Proof. exact (eq_refl (@EL _28366 n)). Qed.
Lemma lem1207332 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term140 _28366 _28367 n f) = (term142 _28366 n).
Proof. exact (MK_COMB (@lem1207331 _28366 n) (@lem1207330 _28366 _28367 f)). Qed.
Lemma lem1207333 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term139 _28366 _28367 n f) = (term142 _28366 n).
Proof. exact (TRANS (@lem1207325 _28366 _28367 n f) (@lem1207332 _28366 _28367 f n)). Qed.
Lemma lem1207334 {_28366 : Type'} : (@eq _28366) = (@eq _28366).
Proof. exact (eq_refl (@eq _28366)). Qed.
Lemma lem1207335 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term143 _28366 _28367 n f) = (term144 _28366 n).
Proof. exact (MK_COMB (@lem1207334 _28366) (@lem1207333 _28366 _28367 f n)). Qed.
Lemma lem1207337 {_25569 : Type'} (n : nat) (l : list _25569) : (term137 _25569 n l) = (term138 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1207338 {_28367 : Type'} (n : nat) (l : list _28367) : (term137 _28367 n l) = (term138 _28367 n l).
Proof. exact (@lem1207337 _28367 n l). Qed.
Lemma lem1207339 {_28367 : Type'} (n : nat) : (term145 _28367 n) = (term142 _28367 n).
Proof. exact (@lem1207338 _28367 n (@nil _28367)). Qed.
Lemma lem1207340 {_28366 _28367 : Type'} (f : _28367 -> _28366) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1207341 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term146 _28366 _28367 f n) = (term147 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207340 _28366 _28367 f) (@lem1207339 _28367 n)). Qed.
Lemma lem1207342 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : ((term139 _28366 _28367 n f) = (term146 _28366 _28367 f n)) = ((term142 _28366 n) = (term147 _28366 _28367 f n)).
Proof. exact (MK_COMB (@lem1207335 _28366 _28367 f n) (@lem1207341 _28366 _28367 f n)). Qed.
Lemma lem1207345 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term61 _28366 _28367 f n) = (term148 _28366 _28367 f n).
Proof. exact (MK_COMB (@lem1207319 _28367 n) (@lem1207342 _28366 _28367 f n)). Qed.
Lemma lem1207347 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1207348 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term148 _28366 _28367 f n) = True.
Proof. exact (@lem1207347 ((term142 _28366 n) = (term147 _28366 _28367 f n))). Qed.
Lemma lem1207349 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : (term61 _28366 _28367 f n) = True.
Proof. exact (TRANS (@lem1207345 _28366 _28367 f n) (@lem1207348 _28366 _28367 f n)). Qed.
Lemma lem1207350 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : True = (term61 _28366 _28367 f n).
Proof. exact (SYM (@lem1207349 _28366 _28367 f n)). Qed.
Lemma lem1207351 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : term61 _28366 _28367 f n.
Proof. exact (EQ_MP (@lem1207350 _28366 _28367 f n) (@lem0)). Qed.
Lemma lem1207352 (m : nat) : term149 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1207353 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem1207354 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem1207353 m) (@lem1207352 m)). Qed.
Lemma lem1207355 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem1207354 m n). Qed.
Lemma lem1207356 (m : nat) (n : nat) : (term151 m n) = ((term152 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem1207358 {A B : Type'} : term104 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1207359 {A B : Type'} (f : A -> B) : term105 A B f.
Proof. exact (@lem1207358 A B f). Qed.
Lemma lem1207360 {A B : Type'} (f : A -> B) : (term105 A B f) = (term106 A B f).
Proof. exact (eq_refl (term105 A B f)). Qed.
Lemma lem1207361 {A B : Type'} (f : A -> B) : term106 A B f.
Proof. exact (EQ_MP (@lem1207360 A B f) (@lem1207359 A B f)). Qed.
Lemma lem1207362 {A B : Type'} (f : A -> B) (h : A) : term107 A B f h.
Proof. exact (@lem1207361 A B f h). Qed.
Lemma lem1207363 {A B : Type'} (h : A) (f : A -> B) : (term107 A B f h) = (term108 A B h f).
Proof. exact (eq_refl (term107 A B f h)). Qed.
Lemma lem1207364 {A B : Type'} (h : A) (f : A -> B) : term108 A B h f.
Proof. exact (EQ_MP (@lem1207363 A B h f) (@lem1207362 A B f h)). Qed.
Lemma lem1207365 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term109 A B h f t.
Proof. exact (@lem1207364 A B h f t). Qed.
Lemma lem1207366 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term109 A B h f t) = ((term110 A B f h t) = (term111 A B h f t)).
Proof. exact (eq_refl (term109 A B h f t)). Qed.
Lemma lem1207382 {A : Type'} : term114 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1207383 {A : Type'} (h : A) : term115 A h.
Proof. exact (@lem1207382 A h). Qed.
Lemma lem1207384 {A : Type'} (h : A) : (term115 A h) = (term116 A h).
Proof. exact (eq_refl (term115 A h)). Qed.
Lemma lem1207385 {A : Type'} (h : A) : term116 A h.
Proof. exact (EQ_MP (@lem1207384 A h) (@lem1207383 A h)). Qed.
Lemma lem1207386 {A : Type'} (h : A) (t : list A) : term117 A h t.
Proof. exact (@lem1207385 A h t). Qed.
Lemma lem1207387 {A : Type'} (h : A) (t : list A) : (term117 A h t) = ((term118 A h t) = (term119 A t)).
Proof. exact (eq_refl (term117 A h t)). Qed.
Lemma lem1207390 {_28366 _28367 : Type'} (l : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term153 _28366 _28367 f n l.
Proof. exact (@lem1207031 _28366 _28367 f n h1 l). Qed.
Lemma lem1207391 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (l : list _28367) : (term153 _28366 _28367 f n l) = (term154 _28366 _28367 f n l).
Proof. exact (eq_refl (term153 _28366 _28367 f n l)). Qed.
Lemma lem1207392 {_28366 _28367 : Type'} (l : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term154 _28366 _28367 f n l.
Proof. exact (EQ_MP (@lem1207391 _28366 _28367 f n l) (@lem1207390 _28366 _28367 l f n h1)). Qed.
Lemma lem1207393 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (l : list _28367) : (term154 _28366 _28367 f n l) = ((term154 _28366 _28367 f n l) = True).
Proof. exact (@lem7 (term154 _28366 _28367 f n l)). Qed.
Lemma lem1207400 {A : Type'} (h : A) (t : list A) : (term118 A h t) = (term119 A t).
Proof. exact (EQ_MP (@lem1207387 A h t) (@lem1207386 A h t)). Qed.
Lemma lem1207401 {_28367 : Type'} (h : _28367) (t : list _28367) : (term118 _28367 h t) = (term119 _28367 t).
Proof. exact (@lem1207400 _28367 h t). Qed.
Lemma lem1207402 (n : nat) : (term133 n) = (term133 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem1207403 {_28367 : Type'} (h : _28367) (n : nat) (t : list _28367) : (term155 _28367 n h t) = (term156 _28367 n t).
Proof. exact (MK_COMB (@lem1207402 n) (@lem1207401 _28367 h t)). Qed.
Lemma lem1207405 (m : nat) (n : nat) : (term152 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1207356 m n) (@lem1207355 m n)). Qed.
Lemma lem1207406 {_28367 : Type'} (n : nat) (t : list _28367) : (term156 _28367 n t) = (term157 _28367 n t).
Proof. exact (@lem1207405 n (@List.length _28367 t)). Qed.
Lemma lem1207407 {_28367 : Type'} (h : _28367) (n : nat) (t : list _28367) : (term155 _28367 n h t) = (term157 _28367 n t).
Proof. exact (TRANS (@lem1207403 _28367 h n t) (@lem1207406 _28367 n t)). Qed.
Lemma lem1207408 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207409 {_28367 : Type'} (h : _28367) (n : nat) (t : list _28367) : (term158 _28367 n h t) = (term159 _28367 n t).
Proof. exact (MK_COMB (@lem1207408) (@lem1207407 _28367 h n t)). Qed.
Lemma lem1207413 {_25569 : Type'} (n : nat) (l : list _25569) : (term137 _25569 n l) = (term138 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1207414 {_28366 : Type'} (n : nat) (l : list _28366) : (term137 _28366 n l) = (term138 _28366 n l).
Proof. exact (@lem1207413 _28366 n l). Qed.
Lemma lem1207415 {_28366 _28367 : Type'} (n : nat) (f : _28367 -> _28366) (h : _28367) (t : list _28367) : (term160 _28366 _28367 n f h t) = (term161 _28366 _28367 n f h t).
Proof. exact (@lem1207414 _28366 n (term125 _28366 _28367 f h t)). Qed.
Lemma lem1207417 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term110 A B f h t) = (term111 A B h f t).
Proof. exact (EQ_MP (@lem1207366 A B h f t) (@lem1207365 A B h f t)). Qed.
Lemma lem1207418 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term125 _28366 _28367 f h t) = (term126 _28366 _28367 h f t).
Proof. exact (@lem1207417 _28367 _28366 h f t). Qed.
Lemma lem1207419 {_28366 : Type'} : (@tl _28366) = (@tl _28366).
Proof. exact (eq_refl (@tl _28366)). Qed.
Lemma lem1207420 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term162 _28366 _28367 f h t) = (term163 _28366 _28367 h f t).
Proof. exact (MK_COMB (@lem1207419 _28366) (@lem1207418 _28366 _28367 h f t)). Qed.
Lemma lem1207422 {A : Type'} (h : A) (t : list A) : (term164 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1207423 {_28366 : Type'} (h : _28366) (t : list _28366) : (term164 _28366 h t) = t.
Proof. exact (@lem1207422 _28366 h t). Qed.
Lemma lem1207424 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term163 _28366 _28367 h f t) = (@List.map _28367 _28366 f t).
Proof. exact (@lem1207423 _28366 (f h) (@List.map _28367 _28366 f t)). Qed.
Lemma lem1207425 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (t : list _28367) : (term162 _28366 _28367 f h t) = (@List.map _28367 _28366 f t).
Proof. exact (TRANS (@lem1207420 _28366 _28367 h f t) (@lem1207424 _28366 _28367 h f t)). Qed.
Lemma lem1207426 {_28366 : Type'} (n : nat) : (@EL _28366 n) = (@EL _28366 n).
Proof. exact (eq_refl (@EL _28366 n)). Qed.
Lemma lem1207427 {_28366 _28367 : Type'} (h : _28367) (n : nat) (f : _28367 -> _28366) (t : list _28367) : (term161 _28366 _28367 n f h t) = (term165 _28366 _28367 n f t).
Proof. exact (MK_COMB (@lem1207426 _28366 n) (@lem1207425 _28366 _28367 h f t)). Qed.
Lemma lem1207428 {_28366 _28367 : Type'} (h : _28367) (n : nat) (f : _28367 -> _28366) (t : list _28367) : (term160 _28366 _28367 n f h t) = (term165 _28366 _28367 n f t).
Proof. exact (TRANS (@lem1207415 _28366 _28367 n f h t) (@lem1207427 _28366 _28367 h n f t)). Qed.
Lemma lem1207429 {_28366 : Type'} : (@eq _28366) = (@eq _28366).
Proof. exact (eq_refl (@eq _28366)). Qed.
Lemma lem1207430 {_28366 _28367 : Type'} (h : _28367) (n : nat) (f : _28367 -> _28366) (t : list _28367) : (term166 _28366 _28367 n f h t) = (term167 _28366 _28367 n f t).
Proof. exact (MK_COMB (@lem1207429 _28366) (@lem1207428 _28366 _28367 h n f t)). Qed.
Lemma lem1207432 {_25569 : Type'} (n : nat) (l : list _25569) : (term137 _25569 n l) = (term138 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1207433 {_28367 : Type'} (n : nat) (l : list _28367) : (term137 _28367 n l) = (term138 _28367 n l).
Proof. exact (@lem1207432 _28367 n l). Qed.
Lemma lem1207434 {_28367 : Type'} (n : nat) (h : _28367) (t : list _28367) : (term168 _28367 n h t) = (term169 _28367 n h t).
Proof. exact (@lem1207433 _28367 n (@cons _28367 h t)). Qed.
Lemma lem1207436 {A : Type'} (h : A) (t : list A) : (term164 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1207437 {_28367 : Type'} (h : _28367) (t : list _28367) : (term164 _28367 h t) = t.
Proof. exact (@lem1207436 _28367 h t). Qed.
Lemma lem1207438 {_28367 : Type'} (n : nat) : (@EL _28367 n) = (@EL _28367 n).
Proof. exact (eq_refl (@EL _28367 n)). Qed.
Lemma lem1207439 {_28367 : Type'} (h : _28367) (n : nat) (t : list _28367) : (term169 _28367 n h t) = (@EL _28367 n t).
Proof. exact (MK_COMB (@lem1207438 _28367 n) (@lem1207437 _28367 h t)). Qed.
Lemma lem1207440 {_28367 : Type'} (h : _28367) (n : nat) (t : list _28367) : (term168 _28367 n h t) = (@EL _28367 n t).
Proof. exact (TRANS (@lem1207434 _28367 n h t) (@lem1207439 _28367 h n t)). Qed.
Lemma lem1207441 {_28366 _28367 : Type'} (f : _28367 -> _28366) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1207442 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (n : nat) (t : list _28367) : (term170 _28366 _28367 f n h t) = (term171 _28366 _28367 f n t).
Proof. exact (MK_COMB (@lem1207441 _28366 _28367 f) (@lem1207440 _28367 h n t)). Qed.
Lemma lem1207443 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (n : nat) (t : list _28367) : ((term160 _28366 _28367 n f h t) = (term170 _28366 _28367 f n h t)) = ((term165 _28366 _28367 n f t) = (term171 _28366 _28367 f n t)).
Proof. exact (MK_COMB (@lem1207430 _28366 _28367 h n f t) (@lem1207442 _28366 _28367 h f n t)). Qed.
Lemma lem1207446 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (n : nat) (t : list _28367) : (term69 _28366 _28367 f n h t) = (term154 _28366 _28367 f n t).
Proof. exact (MK_COMB (@lem1207409 _28367 h n t) (@lem1207443 _28366 _28367 h f n t)). Qed.
Lemma lem1207448 {_28366 _28367 : Type'} (l : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : (term154 _28366 _28367 f n l) = True.
Proof. exact (EQ_MP (@lem1207393 _28366 _28367 f n l) (@lem1207392 _28366 _28367 l f n h1)). Qed.
Lemma lem1207449 {_28366 _28367 : Type'} (l : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : (term154 _28366 _28367 f n l) = True.
Proof. exact (@lem1207448 _28366 _28367 l f n h1). Qed.
Lemma lem1207450 {_28366 _28367 : Type'} (t : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : (term154 _28366 _28367 f n t) = True.
Proof. exact (@lem1207449 _28366 _28367 t f n h1). Qed.
Lemma lem1207451 {_28366 _28367 : Type'} (h : _28367) (t : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : (term69 _28366 _28367 f n h t) = True.
Proof. exact (TRANS (@lem1207446 _28366 _28367 h f n t) (@lem1207450 _28366 _28367 t f n h1)). Qed.
Lemma lem1207452 {_28366 _28367 : Type'} (h : _28367) (t : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : True = (term69 _28366 _28367 f n h t).
Proof. exact (SYM (@lem1207451 _28366 _28367 h t f n h1)). Qed.
Lemma lem1207453 {_28366 _28367 : Type'} (h : _28367) (t : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term69 _28366 _28367 f n h t.
Proof. exact (EQ_MP (@lem1207452 _28366 _28367 h t f n h1) (@lem0)). Qed.
Lemma lem1207454 {_28366 _28367 : Type'} (h : _28367) (t : list _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term71 _28366 _28367 f n h t.
Proof. exact (fun h0 : term65 _28366 _28367 f n t => @lem1207453 _28366 _28367 h t f n h1). Qed.
Lemma lem1207459 {_28366 _28367 : Type'} (h : _28367) (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term75 _28366 _28367 f n h.
Proof. exact (fun t : list _28367 => @lem1207454 _28366 _28367 h t f n h1). Qed.
Lemma lem1207464 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term79 _28366 _28367 f n.
Proof. exact (fun h : _28367 => @lem1207459 _28366 _28367 h f n h1). Qed.
Lemma lem1207465 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term81 _28366 _28367 f n.
Proof. exact (conj (@lem1207351 _28366 _28367 f n) (@lem1207464 _28366 _28367 f n h1)). Qed.
Lemma lem1207466 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) (h1 : term9 _28366 _28367 f n) : term13 _28366 _28367 f n.
Proof. exact (@lem1207086 _28366 _28367 f n (@lem1207465 _28366 _28367 f n h1)). Qed.
Lemma lem1207467 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) (t : list _28367) : term42 _28366 _28367 f h t.
Proof. exact (fun h0 : term36 _28366 _28367 f t => @lem1207263 _28366 _28367 f h t). Qed.
Lemma lem1207472 {_28366 _28367 : Type'} (f : _28367 -> _28366) (h : _28367) : term46 _28366 _28367 f h.
Proof. exact (fun t : list _28367 => @lem1207467 _28366 _28367 f h t). Qed.
Lemma lem1207477 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term50 _28366 _28367 f.
Proof. exact (fun h : _28367 => @lem1207472 _28366 _28367 f h). Qed.
Lemma lem1207478 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term52 _28366 _28367 f.
Proof. exact (conj (@lem1207168 _28366 _28367 f) (@lem1207477 _28366 _28367 f)). Qed.
Lemma lem1207479 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term5 _28366 _28367 f.
Proof. exact (@lem1207058 _28366 _28367 f (@lem1207478 _28366 _28367 f)). Qed.
Lemma lem1207480 {_28366 _28367 : Type'} (f : _28367 -> _28366) (n : nat) : term15 _28366 _28367 f n.
Proof. exact (fun h0 : term9 _28366 _28367 f n => @lem1207466 _28366 _28367 f n h0). Qed.
Lemma lem1207485 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term19 _28366 _28367 f.
Proof. exact (fun n : nat => @lem1207480 _28366 _28367 f n). Qed.
Lemma lem1207486 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term21 _28366 _28367 f.
Proof. exact (conj (@lem1207479 _28366 _28367 f) (@lem1207485 _28366 _28367 f)). Qed.
Lemma lem1207487 {_28366 _28367 : Type'} (f : _28367 -> _28366) : term26 _28366 _28367 f.
Proof. exact (@lem1207030 _28366 _28367 f (@lem1207486 _28366 _28367 f)). Qed.
Lemma lem1207492 {_28366 _28367 : Type'} : term172 _28366 _28367.
Proof. exact (fun f : _28367 -> _28366 => @lem1207487 _28366 _28367 f). Qed.
