Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNIONS_LE_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import CARD_UNION_LE_spec.
Require Import CONJ_ASSOC_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_FINITE_UNIONS_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import HAS_SIZE_spec.
Require Import INT_POS_spec.
Require Import IN_INSERT_spec.
Require Import LE_0_spec.
Require Import LE_TRANS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032046_spec.
Require Import thm1032062_spec.
Require Import thm1032084_spec.
Require Import thm1032118_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19699_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3926943 (a : nat) (b : nat) (x : nat) (n : nat) : (term0 a b x n) = (term1 a b x n).
Proof. exact (@lem17045 (Peano.le a n) (term2 b x n)). Qed.
Lemma lem3926944 (a : nat) (b : nat) (x : nat) (n : nat) : (term3 a b x n) = (term3 a b x n).
Proof. exact (eq_refl (term3 a b x n)). Qed.
Lemma lem3926945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3926946 (a : nat) (b : nat) (x : nat) (n : nat) : (term4 a b x n) = (term5 a b x n).
Proof. exact (MK_COMB (@lem3926945) (@lem3926943 a b x n)). Qed.
Lemma lem3926947 (a : nat) (b : nat) (x : nat) (n : nat) : (term6 a b x n) = (term7 a b x n).
Proof. exact (MK_COMB (@lem3926946 a b x n) (@lem3926944 a b x n)). Qed.
Lemma lem3926948 (a : nat) (b : nat) (x : nat) (n : nat) : (term8 a b x n) = (term6 a b x n).
Proof. exact (@lem17265 (term9 a b x n) (term3 a b x n)). Qed.
Lemma lem3926960 (a : nat) (b : nat) (x : nat) (n : nat) : (term8 a b x n) = (term7 a b x n).
Proof. exact (TRANS (@lem3926948 a b x n) (@lem3926947 a b x n)). Qed.
Lemma lem3926962 (m : nat) : (S m) = (term10 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem3926963 (x : nat) : (S x) = (term10 x).
Proof. exact (@lem3926962 x). Qed.
Lemma lem3926964 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem3926965 (x : nat) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem3926964) (@lem3926963 x)). Qed.
Lemma lem3926966 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3926967 (x : nat) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (MK_COMB (@lem3926965 x) (@lem3926966 n)). Qed.
Lemma lem3926968 (a : nat) (b : nat) : (term15 a b) = (term15 a b).
Proof. exact (eq_refl (term15 a b)). Qed.
Lemma lem3926969 (a : nat) (b : nat) (x : nat) (n : nat) : (term3 a b x n) = (term16 a b x n).
Proof. exact (MK_COMB (@lem3926968 a b) (@lem3926967 x n)). Qed.
Lemma lem3926970 (a : nat) (b : nat) (x : nat) (n : nat) : (term5 a b x n) = (term5 a b x n).
Proof. exact (eq_refl (term5 a b x n)). Qed.
Lemma lem3926971 (a : nat) (b : nat) (x : nat) (n : nat) : (term7 a b x n) = (term17 a b x n).
Proof. exact (MK_COMB (@lem3926970 a b x n) (@lem3926969 a b x n)). Qed.
Lemma lem3926972 (a : nat) (b : nat) (x : nat) (n : nat) : (term8 a b x n) = (term17 a b x n).
Proof. exact (TRANS (@lem3926960 a b x n) (@lem3926971 a b x n)). Qed.
Lemma lem3926984 (n : nat) (x : nat) : (term14 x n) = (term18 n x).
Proof. exact (@lem1032062 n (term10 x)). Qed.
Lemma lem3926985 (x : nat) (n : nat) : (term18 n x) = (term19 x n).
Proof. exact (@lem1032118 x n term20). Qed.
Lemma lem3926986 (n : nat) : (term21 n) = (term22 n).
Proof. exact (@lem1032084 term20 n). Qed.
Lemma lem3926987 (n : nat) : (term22 n) = n.
Proof. exact (@lem1032046 n). Qed.
Lemma lem3926988 (n : nat) : (term21 n) = n.
Proof. exact (TRANS (@lem3926986 n) (@lem3926987 n)). Qed.
Lemma lem3926991 (n : nat) (x : nat) : (term23 n x) = (term23 n x).
Proof. exact (eq_refl (term23 n x)). Qed.
Lemma lem3926992 (x : nat) (n : nat) : (term19 x n) = (term24 x n).
Proof. exact (MK_COMB (@lem3926991 n x) (@lem3926988 n)). Qed.
Lemma lem3926993 (x : nat) (n : nat) : (term18 n x) = (term24 x n).
Proof. exact (TRANS (@lem3926985 x n) (@lem3926992 x n)). Qed.
Lemma lem3926995 (x : nat) (n : nat) : (term14 x n) = (term24 x n).
Proof. exact (TRANS (@lem3926984 n x) (@lem3926993 x n)). Qed.
Lemma lem3927004 (a : nat) (b : nat) : (term15 a b) = (term15 a b).
Proof. exact (eq_refl (term15 a b)). Qed.
Lemma lem3927005 (a : nat) (b : nat) (x : nat) (n : nat) : (term16 a b x n) = (term25 a b x n).
Proof. exact (MK_COMB (@lem3927004 a b) (@lem3926995 x n)). Qed.
Lemma lem3927012 (n : nat) (x : nat) : (Nat.mul x n) = (Nat.mul n x).
Proof. exact (@lem1032084 n x). Qed.
Lemma lem3927015 (b : nat) : (Peano.le b) = (Peano.le b).
Proof. exact (eq_refl (Peano.le b)). Qed.
Lemma lem3927016 (b : nat) (n : nat) (x : nat) : (term2 b x n) = (term2 b n x).
Proof. exact (MK_COMB (@lem3927015 b) (@lem3927012 n x)). Qed.
Lemma lem3927017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3927018 (b : nat) (n : nat) (x : nat) : (term26 b x n) = (term26 b n x).
Proof. exact (MK_COMB (@lem3927017) (@lem3927016 b n x)). Qed.
Lemma lem3927027 (a : nat) (n : nat) : (term27 a n) = (term27 a n).
Proof. exact (eq_refl (term27 a n)). Qed.
Lemma lem3927028 (a : nat) (b : nat) (n : nat) (x : nat) : (term1 a b x n) = (term28 a b n x).
Proof. exact (MK_COMB (@lem3927027 a n) (@lem3927018 b n x)). Qed.
Lemma lem3927029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3927030 (a : nat) (b : nat) (n : nat) (x : nat) : (term5 a b x n) = (term29 a b n x).
Proof. exact (MK_COMB (@lem3927029) (@lem3927028 a b n x)). Qed.
Lemma lem3927031 (a : nat) (b : nat) (x : nat) (n : nat) : (term17 a b x n) = (term30 a b x n).
Proof. exact (MK_COMB (@lem3927030 a b n x) (@lem3927005 a b x n)). Qed.
Lemma lem3927034 (a : nat) (b : nat) (x : nat) (n : nat) : (term8 a b x n) = (term30 a b x n).
Proof. exact (TRANS (@lem3926972 a b x n) (@lem3927031 a b x n)). Qed.
Lemma lem3927036 (m : nat) (n : nat) : (Peano.le m n) = (term31 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3927037 (a : nat) (n : nat) : (Peano.le a n) = (term31 a n).
Proof. exact (@lem3927036 a n). Qed.
Lemma lem3927038 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3927039 (a : nat) (n : nat) : (term32 a n) = (term33 a n).
Proof. exact (MK_COMB (@lem3927038) (@lem3927037 a n)). Qed.
Lemma lem3927040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3927041 (a : nat) (n : nat) : (term27 a n) = (term34 a n).
Proof. exact (MK_COMB (@lem3927040) (@lem3927039 a n)). Qed.
Lemma lem3927043 (m : nat) (n : nat) : (Peano.le m n) = (term31 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3927044 (b : nat) (n : nat) (x : nat) : (term2 b n x) = (term35 b n x).
Proof. exact (@lem3927043 b (Nat.mul n x)). Qed.
Lemma lem3927045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3927046 (b : nat) (n : nat) (x : nat) : (term26 b n x) = (term36 b n x).
Proof. exact (MK_COMB (@lem3927045) (@lem3927044 b n x)). Qed.
Lemma lem3927047 (a : nat) (b : nat) (n : nat) (x : nat) : (term28 a b n x) = (term37 a b n x).
Proof. exact (MK_COMB (@lem3927041 a n) (@lem3927046 b n x)). Qed.
Lemma lem3927048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3927049 (a : nat) (b : nat) (n : nat) (x : nat) : (term29 a b n x) = (term38 a b n x).
Proof. exact (MK_COMB (@lem3927048) (@lem3927047 a b n x)). Qed.
Lemma lem3927051 (m : nat) (n : nat) : (Peano.le m n) = (term31 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3927052 (a : nat) (b : nat) (x : nat) (n : nat) : (term25 a b x n) = (term39 a b x n).
Proof. exact (@lem3927051 (Nat.add a b) (term24 x n)). Qed.
Lemma lem3927054 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3927055 (a : nat) (b : nat) : (term40 a b) = (term41 a b).
Proof. exact (@lem3927054 a b). Qed.
Lemma lem3927056 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem3927057 (a : nat) (b : nat) : (term42 a b) = (term43 a b).
Proof. exact (MK_COMB (@lem3927056) (@lem3927055 a b)). Qed.
Lemma lem3927059 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3927060 (x : nat) (n : nat) : (term44 x n) = (term45 x n).
Proof. exact (@lem3927059 (Nat.mul n x) n). Qed.
Lemma lem3927061 (a : nat) (b : nat) (x : nat) (n : nat) : (term39 a b x n) = (term46 a b x n).
Proof. exact (MK_COMB (@lem3927057 a b) (@lem3927060 x n)). Qed.
Lemma lem3927062 (a : nat) (b : nat) (x : nat) (n : nat) : (term25 a b x n) = (term46 a b x n).
Proof. exact (TRANS (@lem3927052 a b x n) (@lem3927061 a b x n)). Qed.
Lemma lem3927063 (a : nat) (b : nat) (x : nat) (n : nat) : (term30 a b x n) = (term47 a b x n).
Proof. exact (MK_COMB (@lem3927049 a b n x) (@lem3927062 a b x n)). Qed.
Lemma lem3927064 (a : nat) (b : nat) (x : nat) (n : nat) : (term8 a b x n) = (term47 a b x n).
Proof. exact (TRANS (@lem3927034 a b x n) (@lem3927063 a b x n)). Qed.
Lemma lem3927065 (a : nat) : term48 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem3927066 (a : nat) : (term48 a) = (term49 a).
Proof. exact (eq_refl (term48 a)). Qed.
Lemma lem3927067 (a : nat) : term49 a.
Proof. exact (EQ_MP (@lem3927066 a) (@lem3927065 a)). Qed.
Lemma lem3927068 (b : nat) : term48 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem3927069 (b : nat) : (term48 b) = (term49 b).
Proof. exact (eq_refl (term48 b)). Qed.
Lemma lem3927070 (b : nat) : term49 b.
Proof. exact (EQ_MP (@lem3927069 b) (@lem3927068 b)). Qed.
Lemma lem3927071 (n : nat) : term48 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3927072 (n : nat) : (term48 n) = (term49 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem3927073 (n : nat) : term49 n.
Proof. exact (EQ_MP (@lem3927072 n) (@lem3927071 n)). Qed.
Lemma lem3927074 (n : nat) (x : nat) : term50 n x.
Proof. exact (@lem2307535 (Nat.mul n x)). Qed.
Lemma lem3927075 (n : nat) (x : nat) : (term50 n x) = (term51 n x).
Proof. exact (eq_refl (term50 n x)). Qed.
Lemma lem3927076 (n : nat) (x : nat) : term51 n x.
Proof. exact (EQ_MP (@lem3927075 n x) (@lem3927074 n x)). Qed.
Lemma lem3927077 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term52 _45630 _45631 _45633 _45632) = (term53 _45630 _45631 _45633 _45632).
Proof. exact (@lem2318604 (term53 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927101 (_45630 : int) (_45632 : int) : (term54 _45630 _45632) = (int_le _45630 _45632).
Proof. exact (@lem16933 (int_le _45630 _45632)). Qed.
Lemma lem3927104 (_45631 : int) (_45633 : int) : (term54 _45631 _45633) = (int_le _45631 _45633).
Proof. exact (@lem16933 (int_le _45631 _45633)). Qed.
Lemma lem3927105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927106 (_45630 : int) (_45632 : int) : (term55 _45630 _45632) = (term56 _45630 _45632).
Proof. exact (MK_COMB (@lem3927105) (@lem3927101 _45630 _45632)). Qed.
Lemma lem3927107 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term57 _45630 _45632 _45631 _45633) = (term58 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927106 _45630 _45632) (@lem3927104 _45631 _45633)). Qed.
Lemma lem3927108 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term59 _45630 _45632 _45631 _45633) = (term57 _45630 _45632 _45631 _45633).
Proof. exact (@lem17160 (term60 _45630 _45632) (term60 _45631 _45633)). Qed.
Lemma lem3927109 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term59 _45630 _45632 _45631 _45633) = (term58 _45630 _45632 _45631 _45633).
Proof. exact (TRANS (@lem3927108 _45630 _45632 _45631 _45633) (@lem3927107 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3927110 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term61 _45630 _45631 _45633 _45632) = (term61 _45630 _45631 _45633 _45632).
Proof. exact (eq_refl (term61 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927112 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term62 _45630 _45632 _45631 _45633) = (term63 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927111) (@lem3927109 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3927113 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term64 _45630 _45631 _45633 _45632) = (term65 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3927112 _45630 _45632 _45631 _45633) (@lem3927110 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927114 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term66 _45630 _45631 _45633 _45632) = (term64 _45630 _45631 _45633 _45632).
Proof. exact (@lem17160 (term67 _45630 _45632 _45631 _45633) (term68 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927115 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term66 _45630 _45631 _45633 _45632) = (term65 _45630 _45631 _45633 _45632).
Proof. exact (TRANS (@lem3927114 _45630 _45631 _45633 _45632) (@lem3927113 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927117 (_45633 : int) : (term69 _45633) = (term69 _45633).
Proof. exact (eq_refl (term69 _45633)). Qed.
Lemma lem3927118 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term70 _45630 _45631 _45633 _45632) = (term71 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3927117 _45633) (@lem3927115 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927119 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term72 _45630 _45631 _45633 _45632) = (term70 _45630 _45631 _45633 _45632).
Proof. exact (@lem17362 (term73 _45633) (term74 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927120 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term72 _45630 _45631 _45633 _45632) = (term71 _45630 _45631 _45633 _45632).
Proof. exact (TRANS (@lem3927119 _45630 _45631 _45633 _45632) (@lem3927118 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927122 (_45632 : int) : (term69 _45632) = (term69 _45632).
Proof. exact (eq_refl (term69 _45632)). Qed.
Lemma lem3927123 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term75 _45630 _45631 _45633 _45632) = (term76 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3927122 _45632) (@lem3927120 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927124 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term77 _45630 _45631 _45633 _45632) = (term75 _45630 _45631 _45633 _45632).
Proof. exact (@lem17362 (term73 _45632) (term78 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927125 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term77 _45630 _45631 _45633 _45632) = (term76 _45630 _45631 _45633 _45632).
Proof. exact (TRANS (@lem3927124 _45630 _45631 _45633 _45632) (@lem3927123 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927127 (_45631 : int) : (term69 _45631) = (term69 _45631).
Proof. exact (eq_refl (term69 _45631)). Qed.
Lemma lem3927128 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term79 _45630 _45631 _45633 _45632) = (term80 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3927127 _45631) (@lem3927125 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927129 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term81 _45630 _45631 _45633 _45632) = (term79 _45630 _45631 _45633 _45632).
Proof. exact (@lem17362 (term73 _45631) (term82 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927130 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term81 _45630 _45631 _45633 _45632) = (term80 _45630 _45631 _45633 _45632).
Proof. exact (TRANS (@lem3927129 _45630 _45631 _45633 _45632) (@lem3927128 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927132 (_45630 : int) : (term69 _45630) = (term69 _45630).
Proof. exact (eq_refl (term69 _45630)). Qed.
Lemma lem3927133 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term83 _45630 _45631 _45633 _45632) = (term84 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3927132 _45630) (@lem3927130 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927134 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term85 _45630 _45631 _45633 _45632) = (term83 _45630 _45631 _45633 _45632).
Proof. exact (@lem17362 (term73 _45630) (term86 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927164 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term85 _45630 _45631 _45633 _45632) = (term84 _45630 _45631 _45633 _45632).
Proof. exact (TRANS (@lem3927134 _45630 _45631 _45633 _45632) (@lem3927133 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3927167 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927168 (_45630 : int) : (term73 _45630) = (term88 _45630).
Proof. exact (@lem3927167 term89 _45630). Qed.
Lemma lem3927170 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3927171 : term91 = term92.
Proof. exact (@lem3927170 (NUMERAL 0)). Qed.
Lemma lem3927172 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3927173 : term93 = term94.
Proof. exact (MK_COMB (@lem3927172) (@lem3927171)). Qed.
Lemma lem3927174 (_45630 : int) : (real_of_int _45630) = (real_of_int _45630).
Proof. exact (eq_refl (real_of_int _45630)). Qed.
Lemma lem3927175 (_45630 : int) : (term88 _45630) = (term95 _45630).
Proof. exact (MK_COMB (@lem3927173) (@lem3927174 _45630)). Qed.
Lemma lem3927177 (_45630 : int) : (term73 _45630) = (term95 _45630).
Proof. exact (TRANS (@lem3927168 _45630) (@lem3927175 _45630)). Qed.
Lemma lem3927180 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927181 (_45631 : int) : (term73 _45631) = (term88 _45631).
Proof. exact (@lem3927180 term89 _45631). Qed.
Lemma lem3927183 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3927184 : term91 = term92.
Proof. exact (@lem3927183 (NUMERAL 0)). Qed.
Lemma lem3927185 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3927186 : term93 = term94.
Proof. exact (MK_COMB (@lem3927185) (@lem3927184)). Qed.
Lemma lem3927187 (_45631 : int) : (real_of_int _45631) = (real_of_int _45631).
Proof. exact (eq_refl (real_of_int _45631)). Qed.
Lemma lem3927188 (_45631 : int) : (term88 _45631) = (term95 _45631).
Proof. exact (MK_COMB (@lem3927186) (@lem3927187 _45631)). Qed.
Lemma lem3927190 (_45631 : int) : (term73 _45631) = (term95 _45631).
Proof. exact (TRANS (@lem3927181 _45631) (@lem3927188 _45631)). Qed.
Lemma lem3927193 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927194 (_45632 : int) : (term73 _45632) = (term88 _45632).
Proof. exact (@lem3927193 term89 _45632). Qed.
Lemma lem3927196 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3927197 : term91 = term92.
Proof. exact (@lem3927196 (NUMERAL 0)). Qed.
Lemma lem3927198 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3927199 : term93 = term94.
Proof. exact (MK_COMB (@lem3927198) (@lem3927197)). Qed.
Lemma lem3927200 (_45632 : int) : (real_of_int _45632) = (real_of_int _45632).
Proof. exact (eq_refl (real_of_int _45632)). Qed.
Lemma lem3927201 (_45632 : int) : (term88 _45632) = (term95 _45632).
Proof. exact (MK_COMB (@lem3927199) (@lem3927200 _45632)). Qed.
Lemma lem3927203 (_45632 : int) : (term73 _45632) = (term95 _45632).
Proof. exact (TRANS (@lem3927194 _45632) (@lem3927201 _45632)). Qed.
Lemma lem3927206 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927207 (_45633 : int) : (term73 _45633) = (term88 _45633).
Proof. exact (@lem3927206 term89 _45633). Qed.
Lemma lem3927209 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3927210 : term91 = term92.
Proof. exact (@lem3927209 (NUMERAL 0)). Qed.
Lemma lem3927211 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3927212 : term93 = term94.
Proof. exact (MK_COMB (@lem3927211) (@lem3927210)). Qed.
Lemma lem3927213 (_45633 : int) : (real_of_int _45633) = (real_of_int _45633).
Proof. exact (eq_refl (real_of_int _45633)). Qed.
Lemma lem3927214 (_45633 : int) : (term88 _45633) = (term95 _45633).
Proof. exact (MK_COMB (@lem3927212) (@lem3927213 _45633)). Qed.
Lemma lem3927216 (_45633 : int) : (term73 _45633) = (term95 _45633).
Proof. exact (TRANS (@lem3927207 _45633) (@lem3927214 _45633)). Qed.
Lemma lem3927219 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927221 (_45630 : int) (_45632 : int) : (int_le _45630 _45632) = (term87 _45630 _45632).
Proof. exact (@lem3927219 _45630 _45632). Qed.
Lemma lem3927224 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927226 (_45631 : int) (_45633 : int) : (int_le _45631 _45633) = (term87 _45631 _45633).
Proof. exact (@lem3927224 _45631 _45633). Qed.
Lemma lem3927227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927228 (_45630 : int) (_45632 : int) : (term56 _45630 _45632) = (term96 _45630 _45632).
Proof. exact (MK_COMB (@lem3927227) (@lem3927221 _45630 _45632)). Qed.
Lemma lem3927229 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term58 _45630 _45632 _45631 _45633) = (term97 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927228 _45630 _45632) (@lem3927226 _45631 _45633)). Qed.
Lemma lem3927231 (y : int) (x : int) : (term60 x y) = (term98 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3927232 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term61 _45630 _45631 _45633 _45632) = (term99 _45633 _45632 _45630 _45631).
Proof. exact (@lem3927231 (int_add _45633 _45632) (int_add _45630 _45631)). Qed.
Lemma lem3927234 (x : int) (y : int) : (int_le x y) = (term87 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3927235 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term99 _45633 _45632 _45630 _45631) = (term100 _45633 _45632 _45630 _45631).
Proof. exact (@lem3927234 (term101 _45633 _45632) (int_add _45630 _45631)). Qed.
Lemma lem3927237 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3927238 (_45633 : int) (_45632 : int) : (term104 _45633 _45632) = (term105 _45633 _45632).
Proof. exact (@lem3927237 (int_add _45633 _45632) term106). Qed.
Lemma lem3927240 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3927241 (_45633 : int) (_45632 : int) : (term102 _45633 _45632) = (term103 _45633 _45632).
Proof. exact (@lem3927240 _45633 _45632). Qed.
Lemma lem3927242 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3927243 (_45633 : int) (_45632 : int) : (term107 _45633 _45632) = (term108 _45633 _45632).
Proof. exact (MK_COMB (@lem3927242) (@lem3927241 _45633 _45632)). Qed.
Lemma lem3927245 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3927246 : term109 = term110.
Proof. exact (@lem3927245 term20). Qed.
Lemma lem3927247 (_45633 : int) (_45632 : int) : (term105 _45633 _45632) = (term111 _45633 _45632).
Proof. exact (MK_COMB (@lem3927243 _45633 _45632) (@lem3927246)). Qed.
Lemma lem3927248 (_45633 : int) (_45632 : int) : (term104 _45633 _45632) = (term111 _45633 _45632).
Proof. exact (TRANS (@lem3927238 _45633 _45632) (@lem3927247 _45633 _45632)). Qed.
Lemma lem3927249 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3927250 (_45633 : int) (_45632 : int) : (term112 _45633 _45632) = (term113 _45633 _45632).
Proof. exact (MK_COMB (@lem3927249) (@lem3927248 _45633 _45632)). Qed.
Lemma lem3927252 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3927253 (_45630 : int) (_45631 : int) : (term102 _45630 _45631) = (term103 _45630 _45631).
Proof. exact (@lem3927252 _45630 _45631). Qed.
Lemma lem3927254 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term100 _45633 _45632 _45630 _45631) = (term114 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927250 _45633 _45632) (@lem3927253 _45630 _45631)). Qed.
Lemma lem3927255 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term99 _45633 _45632 _45630 _45631) = (term114 _45633 _45632 _45630 _45631).
Proof. exact (TRANS (@lem3927235 _45633 _45632 _45630 _45631) (@lem3927254 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927256 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term61 _45630 _45631 _45633 _45632) = (term114 _45633 _45632 _45630 _45631).
Proof. exact (TRANS (@lem3927232 _45633 _45632 _45630 _45631) (@lem3927255 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927258 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term63 _45630 _45632 _45631 _45633) = (term115 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927257) (@lem3927229 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3927259 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term65 _45630 _45631 _45633 _45632) = (term116 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927258 _45630 _45632 _45631 _45633) (@lem3927256 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927261 (_45633 : int) : (term69 _45633) = (term117 _45633).
Proof. exact (MK_COMB (@lem3927260) (@lem3927216 _45633)). Qed.
Lemma lem3927262 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term71 _45630 _45631 _45633 _45632) = (term118 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927261 _45633) (@lem3927259 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927264 (_45632 : int) : (term69 _45632) = (term117 _45632).
Proof. exact (MK_COMB (@lem3927263) (@lem3927203 _45632)). Qed.
Lemma lem3927265 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term76 _45630 _45631 _45633 _45632) = (term119 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927264 _45632) (@lem3927262 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927267 (_45631 : int) : (term69 _45631) = (term117 _45631).
Proof. exact (MK_COMB (@lem3927266) (@lem3927190 _45631)). Qed.
Lemma lem3927268 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term80 _45630 _45631 _45633 _45632) = (term120 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927267 _45631) (@lem3927265 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927270 (_45630 : int) : (term69 _45630) = (term117 _45630).
Proof. exact (MK_COMB (@lem3927269) (@lem3927177 _45630)). Qed.
Lemma lem3927271 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term84 _45630 _45631 _45633 _45632) = (term121 _45633 _45632 _45630 _45631).
Proof. exact (MK_COMB (@lem3927270 _45630) (@lem3927268 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927272 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term85 _45630 _45631 _45633 _45632) = (term121 _45633 _45632 _45630 _45631).
Proof. exact (TRANS (@lem3927164 _45630 _45631 _45633 _45632) (@lem3927271 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927276 (t : Prop) : (term122 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3927342 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : (term123 _45633 _45632 _45630 _45631) = (term121 _45633 _45632 _45630 _45631).
Proof. exact (@lem3927276 (term121 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3927343 (_45630 : int) : (term95 _45630) = (term124 _45630).
Proof. exact (@lem1988287 (real_of_int _45630) term92). Qed.
Lemma lem3927349 (_45630 : int) : (term125 _45630) = (term126 _45630).
Proof. exact (@lem1982792 (real_of_int _45630) term92). Qed.
Lemma lem3927351 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927352 : term92 = term128.
Proof. exact (@lem3927351 (NUMERAL 0)). Qed.
Lemma lem3927354 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927355 : term131 = term132.
Proof. exact (@lem3927354 term20). Qed.
Lemma lem3927356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927357 : term133 = term134.
Proof. exact (MK_COMB (@lem3927356) (@lem3927355)). Qed.
Lemma lem3927358 : term135 = term136.
Proof. exact (MK_COMB (@lem3927357) (@lem3927352)). Qed.
Lemma lem3927359 : term136 = term137.
Proof. exact (@lem1981613 term131 term92 term110 term110). Qed.
Lemma lem3927361 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927362 : term140 = term141.
Proof. exact (@lem3927361 term20 term20). Qed.
Lemma lem3927363 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927364 : term143 = term20.
Proof. exact (EQ_MP (@lem3927363) (@lem940073)). Qed.
Lemma lem3927365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927366 : term141 = term110.
Proof. exact (MK_COMB (@lem3927365) (@lem3927364)). Qed.
Lemma lem3927367 : term140 = term110.
Proof. exact (TRANS (@lem3927362) (@lem3927366)). Qed.
Lemma lem3927369 (x : nat) : (term144 x) = term92.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3927370 : term135 = term92.
Proof. exact (@lem3927369 term20). Qed.
Lemma lem3927371 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3927372 : term145 = term146.
Proof. exact (MK_COMB (@lem3927371) (@lem3927370)). Qed.
Lemma lem3927373 : term137 = term128.
Proof. exact (MK_COMB (@lem3927372) (@lem3927367)). Qed.
Lemma lem3927374 : term136 = term128.
Proof. exact (TRANS (@lem3927359) (@lem3927373)). Qed.
Lemma lem3927375 : term135 = term128.
Proof. exact (TRANS (@lem3927358) (@lem3927374)). Qed.
Lemma lem3927377 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3927378 : term128 = term92.
Proof. exact (@lem3927377 term92). Qed.
Lemma lem3927379 : term135 = term92.
Proof. exact (TRANS (@lem3927375) (@lem3927378)). Qed.
Lemma lem3927380 (_45630 : int) : (term148 _45630) = (term148 _45630).
Proof. exact (eq_refl (term148 _45630)). Qed.
Lemma lem3927381 (_45630 : int) : (term126 _45630) = (term149 _45630).
Proof. exact (MK_COMB (@lem3927380 _45630) (@lem3927379)). Qed.
Lemma lem3927382 (_45630 : int) : (term149 _45630) = (real_of_int _45630).
Proof. exact (@lem1982723 (real_of_int _45630)). Qed.
Lemma lem3927383 (_45630 : int) : (term126 _45630) = (real_of_int _45630).
Proof. exact (TRANS (@lem3927381 _45630) (@lem3927382 _45630)). Qed.
Lemma lem3927385 (_45630 : int) : (term125 _45630) = (real_of_int _45630).
Proof. exact (TRANS (@lem3927349 _45630) (@lem3927383 _45630)). Qed.
Lemma lem3927386 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927387 (_45630 : int) : (term150 _45630) = (term151 _45630).
Proof. exact (MK_COMB (@lem3927386) (@lem3927385 _45630)). Qed.
Lemma lem3927388 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927389 (_45630 : int) : (term124 _45630) = (term152 _45630).
Proof. exact (MK_COMB (@lem3927387 _45630) (@lem3927388)). Qed.
Lemma lem3927390 (_45630 : int) : (term95 _45630) = (term152 _45630).
Proof. exact (TRANS (@lem3927343 _45630) (@lem3927389 _45630)). Qed.
Lemma lem3927391 (_45631 : int) : (term95 _45631) = (term124 _45631).
Proof. exact (@lem1988287 (real_of_int _45631) term92). Qed.
Lemma lem3927397 (_45631 : int) : (term125 _45631) = (term126 _45631).
Proof. exact (@lem1982792 (real_of_int _45631) term92). Qed.
Lemma lem3927399 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927400 : term92 = term128.
Proof. exact (@lem3927399 (NUMERAL 0)). Qed.
Lemma lem3927402 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927403 : term131 = term132.
Proof. exact (@lem3927402 term20). Qed.
Lemma lem3927404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927405 : term133 = term134.
Proof. exact (MK_COMB (@lem3927404) (@lem3927403)). Qed.
Lemma lem3927406 : term135 = term136.
Proof. exact (MK_COMB (@lem3927405) (@lem3927400)). Qed.
Lemma lem3927407 : term136 = term137.
Proof. exact (@lem1981613 term131 term92 term110 term110). Qed.
Lemma lem3927409 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927410 : term140 = term141.
Proof. exact (@lem3927409 term20 term20). Qed.
Lemma lem3927411 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927412 : term143 = term20.
Proof. exact (EQ_MP (@lem3927411) (@lem940073)). Qed.
Lemma lem3927413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927414 : term141 = term110.
Proof. exact (MK_COMB (@lem3927413) (@lem3927412)). Qed.
Lemma lem3927415 : term140 = term110.
Proof. exact (TRANS (@lem3927410) (@lem3927414)). Qed.
Lemma lem3927417 (x : nat) : (term144 x) = term92.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3927418 : term135 = term92.
Proof. exact (@lem3927417 term20). Qed.
Lemma lem3927419 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3927420 : term145 = term146.
Proof. exact (MK_COMB (@lem3927419) (@lem3927418)). Qed.
Lemma lem3927421 : term137 = term128.
Proof. exact (MK_COMB (@lem3927420) (@lem3927415)). Qed.
Lemma lem3927422 : term136 = term128.
Proof. exact (TRANS (@lem3927407) (@lem3927421)). Qed.
Lemma lem3927423 : term135 = term128.
Proof. exact (TRANS (@lem3927406) (@lem3927422)). Qed.
Lemma lem3927425 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3927426 : term128 = term92.
Proof. exact (@lem3927425 term92). Qed.
Lemma lem3927427 : term135 = term92.
Proof. exact (TRANS (@lem3927423) (@lem3927426)). Qed.
Lemma lem3927428 (_45631 : int) : (term148 _45631) = (term148 _45631).
Proof. exact (eq_refl (term148 _45631)). Qed.
Lemma lem3927429 (_45631 : int) : (term126 _45631) = (term149 _45631).
Proof. exact (MK_COMB (@lem3927428 _45631) (@lem3927427)). Qed.
Lemma lem3927430 (_45631 : int) : (term149 _45631) = (real_of_int _45631).
Proof. exact (@lem1982723 (real_of_int _45631)). Qed.
Lemma lem3927431 (_45631 : int) : (term126 _45631) = (real_of_int _45631).
Proof. exact (TRANS (@lem3927429 _45631) (@lem3927430 _45631)). Qed.
Lemma lem3927433 (_45631 : int) : (term125 _45631) = (real_of_int _45631).
Proof. exact (TRANS (@lem3927397 _45631) (@lem3927431 _45631)). Qed.
Lemma lem3927434 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927435 (_45631 : int) : (term150 _45631) = (term151 _45631).
Proof. exact (MK_COMB (@lem3927434) (@lem3927433 _45631)). Qed.
Lemma lem3927436 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927437 (_45631 : int) : (term124 _45631) = (term152 _45631).
Proof. exact (MK_COMB (@lem3927435 _45631) (@lem3927436)). Qed.
Lemma lem3927438 (_45631 : int) : (term95 _45631) = (term152 _45631).
Proof. exact (TRANS (@lem3927391 _45631) (@lem3927437 _45631)). Qed.
Lemma lem3927439 (_45632 : int) : (term95 _45632) = (term124 _45632).
Proof. exact (@lem1988287 (real_of_int _45632) term92). Qed.
Lemma lem3927445 (_45632 : int) : (term125 _45632) = (term126 _45632).
Proof. exact (@lem1982792 (real_of_int _45632) term92). Qed.
Lemma lem3927447 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927448 : term92 = term128.
Proof. exact (@lem3927447 (NUMERAL 0)). Qed.
Lemma lem3927450 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927451 : term131 = term132.
Proof. exact (@lem3927450 term20). Qed.
Lemma lem3927452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927453 : term133 = term134.
Proof. exact (MK_COMB (@lem3927452) (@lem3927451)). Qed.
Lemma lem3927454 : term135 = term136.
Proof. exact (MK_COMB (@lem3927453) (@lem3927448)). Qed.
Lemma lem3927455 : term136 = term137.
Proof. exact (@lem1981613 term131 term92 term110 term110). Qed.
Lemma lem3927457 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927458 : term140 = term141.
Proof. exact (@lem3927457 term20 term20). Qed.
Lemma lem3927459 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927460 : term143 = term20.
Proof. exact (EQ_MP (@lem3927459) (@lem940073)). Qed.
Lemma lem3927461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927462 : term141 = term110.
Proof. exact (MK_COMB (@lem3927461) (@lem3927460)). Qed.
Lemma lem3927463 : term140 = term110.
Proof. exact (TRANS (@lem3927458) (@lem3927462)). Qed.
Lemma lem3927465 (x : nat) : (term144 x) = term92.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3927466 : term135 = term92.
Proof. exact (@lem3927465 term20). Qed.
Lemma lem3927467 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3927468 : term145 = term146.
Proof. exact (MK_COMB (@lem3927467) (@lem3927466)). Qed.
Lemma lem3927469 : term137 = term128.
Proof. exact (MK_COMB (@lem3927468) (@lem3927463)). Qed.
Lemma lem3927470 : term136 = term128.
Proof. exact (TRANS (@lem3927455) (@lem3927469)). Qed.
Lemma lem3927471 : term135 = term128.
Proof. exact (TRANS (@lem3927454) (@lem3927470)). Qed.
Lemma lem3927473 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3927474 : term128 = term92.
Proof. exact (@lem3927473 term92). Qed.
Lemma lem3927475 : term135 = term92.
Proof. exact (TRANS (@lem3927471) (@lem3927474)). Qed.
Lemma lem3927476 (_45632 : int) : (term148 _45632) = (term148 _45632).
Proof. exact (eq_refl (term148 _45632)). Qed.
Lemma lem3927477 (_45632 : int) : (term126 _45632) = (term149 _45632).
Proof. exact (MK_COMB (@lem3927476 _45632) (@lem3927475)). Qed.
Lemma lem3927478 (_45632 : int) : (term149 _45632) = (real_of_int _45632).
Proof. exact (@lem1982723 (real_of_int _45632)). Qed.
Lemma lem3927479 (_45632 : int) : (term126 _45632) = (real_of_int _45632).
Proof. exact (TRANS (@lem3927477 _45632) (@lem3927478 _45632)). Qed.
Lemma lem3927481 (_45632 : int) : (term125 _45632) = (real_of_int _45632).
Proof. exact (TRANS (@lem3927445 _45632) (@lem3927479 _45632)). Qed.
Lemma lem3927482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927483 (_45632 : int) : (term150 _45632) = (term151 _45632).
Proof. exact (MK_COMB (@lem3927482) (@lem3927481 _45632)). Qed.
Lemma lem3927484 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927485 (_45632 : int) : (term124 _45632) = (term152 _45632).
Proof. exact (MK_COMB (@lem3927483 _45632) (@lem3927484)). Qed.
Lemma lem3927486 (_45632 : int) : (term95 _45632) = (term152 _45632).
Proof. exact (TRANS (@lem3927439 _45632) (@lem3927485 _45632)). Qed.
Lemma lem3927487 (_45633 : int) : (term95 _45633) = (term124 _45633).
Proof. exact (@lem1988287 (real_of_int _45633) term92). Qed.
Lemma lem3927493 (_45633 : int) : (term125 _45633) = (term126 _45633).
Proof. exact (@lem1982792 (real_of_int _45633) term92). Qed.
Lemma lem3927495 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927496 : term92 = term128.
Proof. exact (@lem3927495 (NUMERAL 0)). Qed.
Lemma lem3927498 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927499 : term131 = term132.
Proof. exact (@lem3927498 term20). Qed.
Lemma lem3927500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927501 : term133 = term134.
Proof. exact (MK_COMB (@lem3927500) (@lem3927499)). Qed.
Lemma lem3927502 : term135 = term136.
Proof. exact (MK_COMB (@lem3927501) (@lem3927496)). Qed.
Lemma lem3927503 : term136 = term137.
Proof. exact (@lem1981613 term131 term92 term110 term110). Qed.
Lemma lem3927505 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927506 : term140 = term141.
Proof. exact (@lem3927505 term20 term20). Qed.
Lemma lem3927507 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927508 : term143 = term20.
Proof. exact (EQ_MP (@lem3927507) (@lem940073)). Qed.
Lemma lem3927509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927510 : term141 = term110.
Proof. exact (MK_COMB (@lem3927509) (@lem3927508)). Qed.
Lemma lem3927511 : term140 = term110.
Proof. exact (TRANS (@lem3927506) (@lem3927510)). Qed.
Lemma lem3927513 (x : nat) : (term144 x) = term92.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3927514 : term135 = term92.
Proof. exact (@lem3927513 term20). Qed.
Lemma lem3927515 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3927516 : term145 = term146.
Proof. exact (MK_COMB (@lem3927515) (@lem3927514)). Qed.
Lemma lem3927517 : term137 = term128.
Proof. exact (MK_COMB (@lem3927516) (@lem3927511)). Qed.
Lemma lem3927518 : term136 = term128.
Proof. exact (TRANS (@lem3927503) (@lem3927517)). Qed.
Lemma lem3927519 : term135 = term128.
Proof. exact (TRANS (@lem3927502) (@lem3927518)). Qed.
Lemma lem3927521 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3927522 : term128 = term92.
Proof. exact (@lem3927521 term92). Qed.
Lemma lem3927523 : term135 = term92.
Proof. exact (TRANS (@lem3927519) (@lem3927522)). Qed.
Lemma lem3927524 (_45633 : int) : (term148 _45633) = (term148 _45633).
Proof. exact (eq_refl (term148 _45633)). Qed.
Lemma lem3927525 (_45633 : int) : (term126 _45633) = (term149 _45633).
Proof. exact (MK_COMB (@lem3927524 _45633) (@lem3927523)). Qed.
Lemma lem3927526 (_45633 : int) : (term149 _45633) = (real_of_int _45633).
Proof. exact (@lem1982723 (real_of_int _45633)). Qed.
Lemma lem3927527 (_45633 : int) : (term126 _45633) = (real_of_int _45633).
Proof. exact (TRANS (@lem3927525 _45633) (@lem3927526 _45633)). Qed.
Lemma lem3927529 (_45633 : int) : (term125 _45633) = (real_of_int _45633).
Proof. exact (TRANS (@lem3927493 _45633) (@lem3927527 _45633)). Qed.
Lemma lem3927530 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927531 (_45633 : int) : (term150 _45633) = (term151 _45633).
Proof. exact (MK_COMB (@lem3927530) (@lem3927529 _45633)). Qed.
Lemma lem3927532 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927533 (_45633 : int) : (term124 _45633) = (term152 _45633).
Proof. exact (MK_COMB (@lem3927531 _45633) (@lem3927532)). Qed.
Lemma lem3927534 (_45633 : int) : (term95 _45633) = (term152 _45633).
Proof. exact (TRANS (@lem3927487 _45633) (@lem3927533 _45633)). Qed.
Lemma lem3927535 (_45632 : int) (_45630 : int) : (term87 _45630 _45632) = (term153 _45632 _45630).
Proof. exact (@lem1988287 (real_of_int _45632) (real_of_int _45630)). Qed.
Lemma lem3927541 (_45632 : int) (_45630 : int) : (term154 _45632 _45630) = (term155 _45632 _45630).
Proof. exact (@lem1982792 (real_of_int _45632) (real_of_int _45630)). Qed.
Lemma lem3927546 (_45630 : int) (_45632 : int) : (term155 _45632 _45630) = (term156 _45630 _45632).
Proof. exact (@lem1982761 (term157 _45630) (real_of_int _45632)). Qed.
Lemma lem3927548 (_45630 : int) (_45632 : int) : (term154 _45632 _45630) = (term156 _45630 _45632).
Proof. exact (TRANS (@lem3927541 _45632 _45630) (@lem3927546 _45630 _45632)). Qed.
Lemma lem3927549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927550 (_45630 : int) (_45632 : int) : (term158 _45632 _45630) = (term159 _45630 _45632).
Proof. exact (MK_COMB (@lem3927549) (@lem3927548 _45630 _45632)). Qed.
Lemma lem3927551 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927552 (_45630 : int) (_45632 : int) : (term153 _45632 _45630) = (term160 _45630 _45632).
Proof. exact (MK_COMB (@lem3927550 _45630 _45632) (@lem3927551)). Qed.
Lemma lem3927553 (_45630 : int) (_45632 : int) : (term87 _45630 _45632) = (term160 _45630 _45632).
Proof. exact (TRANS (@lem3927535 _45632 _45630) (@lem3927552 _45630 _45632)). Qed.
Lemma lem3927554 (_45633 : int) (_45631 : int) : (term87 _45631 _45633) = (term153 _45633 _45631).
Proof. exact (@lem1988287 (real_of_int _45633) (real_of_int _45631)). Qed.
Lemma lem3927560 (_45633 : int) (_45631 : int) : (term154 _45633 _45631) = (term155 _45633 _45631).
Proof. exact (@lem1982792 (real_of_int _45633) (real_of_int _45631)). Qed.
Lemma lem3927565 (_45631 : int) (_45633 : int) : (term155 _45633 _45631) = (term156 _45631 _45633).
Proof. exact (@lem1982761 (term157 _45631) (real_of_int _45633)). Qed.
Lemma lem3927567 (_45631 : int) (_45633 : int) : (term154 _45633 _45631) = (term156 _45631 _45633).
Proof. exact (TRANS (@lem3927560 _45633 _45631) (@lem3927565 _45631 _45633)). Qed.
Lemma lem3927568 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927569 (_45631 : int) (_45633 : int) : (term158 _45633 _45631) = (term159 _45631 _45633).
Proof. exact (MK_COMB (@lem3927568) (@lem3927567 _45631 _45633)). Qed.
Lemma lem3927570 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927571 (_45631 : int) (_45633 : int) : (term153 _45633 _45631) = (term160 _45631 _45633).
Proof. exact (MK_COMB (@lem3927569 _45631 _45633) (@lem3927570)). Qed.
Lemma lem3927572 (_45631 : int) (_45633 : int) : (term87 _45631 _45633) = (term160 _45631 _45633).
Proof. exact (TRANS (@lem3927554 _45633 _45631) (@lem3927571 _45631 _45633)). Qed.
Lemma lem3927573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927574 (_45630 : int) (_45632 : int) : (term96 _45630 _45632) = (term161 _45630 _45632).
Proof. exact (MK_COMB (@lem3927573) (@lem3927553 _45630 _45632)). Qed.
Lemma lem3927575 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term97 _45630 _45632 _45631 _45633) = (term162 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927574 _45630 _45632) (@lem3927572 _45631 _45633)). Qed.
Lemma lem3927576 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term114 _45633 _45632 _45630 _45631) = (term163 _45630 _45631 _45633 _45632).
Proof. exact (@lem1988287 (term103 _45630 _45631) (term111 _45633 _45632)). Qed.
Lemma lem3927577 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem3927584 (_45632 : int) (_45633 : int) : (term103 _45633 _45632) = (term103 _45632 _45633).
Proof. exact (@lem1982761 (real_of_int _45632) (real_of_int _45633)). Qed.
Lemma lem3927585 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3927586 (_45632 : int) (_45633 : int) : (term108 _45633 _45632) = (term108 _45632 _45633).
Proof. exact (MK_COMB (@lem3927585) (@lem3927584 _45632 _45633)). Qed.
Lemma lem3927587 (_45632 : int) (_45633 : int) : (term111 _45633 _45632) = (term111 _45632 _45633).
Proof. exact (MK_COMB (@lem3927586 _45632 _45633) (@lem3927577)). Qed.
Lemma lem3927592 (_45632 : int) (_45633 : int) : (term111 _45632 _45633) = (term164 _45632 _45633).
Proof. exact (@lem1982755 (real_of_int _45632) (real_of_int _45633) term110). Qed.
Lemma lem3927593 (_45632 : int) (_45633 : int) : (term111 _45633 _45632) = (term164 _45632 _45633).
Proof. exact (TRANS (@lem3927587 _45632 _45633) (@lem3927592 _45632 _45633)). Qed.
Lemma lem3927602 (_45630 : int) (_45631 : int) : (term165 _45630 _45631) = (term165 _45630 _45631).
Proof. exact (eq_refl (term165 _45630 _45631)). Qed.
Lemma lem3927603 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term166 _45630 _45631 _45633 _45632) = (term167 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927602 _45630 _45631) (@lem3927593 _45632 _45633)). Qed.
Lemma lem3927604 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term167 _45630 _45631 _45632 _45633) = (term168 _45630 _45631 _45632 _45633).
Proof. exact (@lem1982792 (term103 _45630 _45631) (term164 _45632 _45633)). Qed.
Lemma lem3927605 (_45632 : int) (_45633 : int) : (term169 _45632 _45633) = (term170 _45632 _45633).
Proof. exact (@lem1982781 (real_of_int _45632) term131 (term171 _45633)). Qed.
Lemma lem3927606 (_45633 : int) : (term172 _45633) = (term173 _45633).
Proof. exact (@lem1982781 (real_of_int _45633) term131 term110). Qed.
Lemma lem3927608 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927609 : term110 = term174.
Proof. exact (@lem3927608 term20). Qed.
Lemma lem3927611 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927612 : term131 = term132.
Proof. exact (@lem3927611 term20). Qed.
Lemma lem3927613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927614 : term133 = term134.
Proof. exact (MK_COMB (@lem3927613) (@lem3927612)). Qed.
Lemma lem3927615 : term175 = term176.
Proof. exact (MK_COMB (@lem3927614) (@lem3927609)). Qed.
Lemma lem3927616 : term176 = term177.
Proof. exact (@lem1981613 term131 term110 term110 term110). Qed.
Lemma lem3927618 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927619 : term140 = term141.
Proof. exact (@lem3927618 term20 term20). Qed.
Lemma lem3927620 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927621 : term143 = term20.
Proof. exact (EQ_MP (@lem3927620) (@lem940073)). Qed.
Lemma lem3927622 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927623 : term141 = term110.
Proof. exact (MK_COMB (@lem3927622) (@lem3927621)). Qed.
Lemma lem3927624 : term140 = term110.
Proof. exact (TRANS (@lem3927619) (@lem3927623)). Qed.
Lemma lem3927626 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3927627 : term175 = term180.
Proof. exact (@lem3927626 term20 term20). Qed.
Lemma lem3927628 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927629 : term143 = term20.
Proof. exact (EQ_MP (@lem3927628) (@lem940073)). Qed.
Lemma lem3927630 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927631 : term141 = term110.
Proof. exact (MK_COMB (@lem3927630) (@lem3927629)). Qed.
Lemma lem3927632 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3927633 : term180 = term131.
Proof. exact (MK_COMB (@lem3927632) (@lem3927631)). Qed.
Lemma lem3927634 : term175 = term131.
Proof. exact (TRANS (@lem3927627) (@lem3927633)). Qed.
Lemma lem3927635 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3927636 : term181 = term182.
Proof. exact (MK_COMB (@lem3927635) (@lem3927634)). Qed.
Lemma lem3927637 : term177 = term132.
Proof. exact (MK_COMB (@lem3927636) (@lem3927624)). Qed.
Lemma lem3927638 : term176 = term132.
Proof. exact (TRANS (@lem3927616) (@lem3927637)). Qed.
Lemma lem3927639 : term175 = term132.
Proof. exact (TRANS (@lem3927615) (@lem3927638)). Qed.
Lemma lem3927641 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3927642 : term132 = term131.
Proof. exact (@lem3927641 term131). Qed.
Lemma lem3927643 : term175 = term131.
Proof. exact (TRANS (@lem3927639) (@lem3927642)). Qed.
Lemma lem3927646 (_45633 : int) : (term183 _45633) = (term183 _45633).
Proof. exact (eq_refl (term183 _45633)). Qed.
Lemma lem3927647 (_45633 : int) : (term173 _45633) = (term184 _45633).
Proof. exact (MK_COMB (@lem3927646 _45633) (@lem3927643)). Qed.
Lemma lem3927648 (_45633 : int) : (term172 _45633) = (term184 _45633).
Proof. exact (TRANS (@lem3927606 _45633) (@lem3927647 _45633)). Qed.
Lemma lem3927651 (_45632 : int) : (term183 _45632) = (term183 _45632).
Proof. exact (eq_refl (term183 _45632)). Qed.
Lemma lem3927652 (_45632 : int) (_45633 : int) : (term170 _45632 _45633) = (term185 _45632 _45633).
Proof. exact (MK_COMB (@lem3927651 _45632) (@lem3927648 _45633)). Qed.
Lemma lem3927653 (_45632 : int) (_45633 : int) : (term169 _45632 _45633) = (term185 _45632 _45633).
Proof. exact (TRANS (@lem3927605 _45632 _45633) (@lem3927652 _45632 _45633)). Qed.
Lemma lem3927654 (_45630 : int) (_45631 : int) : (term108 _45630 _45631) = (term108 _45630 _45631).
Proof. exact (eq_refl (term108 _45630 _45631)). Qed.
Lemma lem3927655 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term168 _45630 _45631 _45632 _45633) = (term186 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927654 _45630 _45631) (@lem3927653 _45632 _45633)). Qed.
Lemma lem3927660 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term186 _45630 _45631 _45632 _45633) = (term187 _45630 _45631 _45632 _45633).
Proof. exact (@lem1982755 (real_of_int _45630) (real_of_int _45631) (term185 _45632 _45633)). Qed.
Lemma lem3927661 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term168 _45630 _45631 _45632 _45633) = (term187 _45630 _45631 _45632 _45633).
Proof. exact (TRANS (@lem3927655 _45630 _45631 _45632 _45633) (@lem3927660 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927662 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term167 _45630 _45631 _45632 _45633) = (term187 _45630 _45631 _45632 _45633).
Proof. exact (TRANS (@lem3927604 _45630 _45631 _45632 _45633) (@lem3927661 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927663 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term166 _45630 _45631 _45633 _45632) = (term187 _45630 _45631 _45632 _45633).
Proof. exact (TRANS (@lem3927603 _45630 _45631 _45632 _45633) (@lem3927662 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927664 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927665 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term188 _45630 _45631 _45633 _45632) = (term189 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927664) (@lem3927663 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927666 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927667 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term163 _45630 _45631 _45633 _45632) = (term190 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927665 _45630 _45631 _45632 _45633) (@lem3927666)). Qed.
Lemma lem3927668 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term114 _45633 _45632 _45630 _45631) = (term190 _45630 _45631 _45632 _45633).
Proof. exact (TRANS (@lem3927576 _45630 _45631 _45633 _45632) (@lem3927667 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927670 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term115 _45630 _45632 _45631 _45633) = (term191 _45630 _45632 _45631 _45633).
Proof. exact (MK_COMB (@lem3927669) (@lem3927575 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3927671 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term116 _45633 _45632 _45630 _45631) = (term192 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927670 _45630 _45632 _45631 _45633) (@lem3927668 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927673 (_45633 : int) : (term117 _45633) = (term193 _45633).
Proof. exact (MK_COMB (@lem3927672) (@lem3927534 _45633)). Qed.
Lemma lem3927674 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term118 _45633 _45632 _45630 _45631) = (term194 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927673 _45633) (@lem3927671 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927676 (_45632 : int) : (term117 _45632) = (term193 _45632).
Proof. exact (MK_COMB (@lem3927675) (@lem3927486 _45632)). Qed.
Lemma lem3927677 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term119 _45633 _45632 _45630 _45631) = (term195 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927676 _45632) (@lem3927674 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927679 (_45631 : int) : (term117 _45631) = (term193 _45631).
Proof. exact (MK_COMB (@lem3927678) (@lem3927438 _45631)). Qed.
Lemma lem3927680 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term120 _45633 _45632 _45630 _45631) = (term196 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927679 _45631) (@lem3927677 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3927682 (_45630 : int) : (term117 _45630) = (term193 _45630).
Proof. exact (MK_COMB (@lem3927681) (@lem3927390 _45630)). Qed.
Lemma lem3927683 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term121 _45633 _45632 _45630 _45631) = (term197 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927682 _45630) (@lem3927680 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927728 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term123 _45633 _45632 _45630 _45631) = (term197 _45630 _45631 _45632 _45633).
Proof. exact (TRANS (@lem3927342 _45633 _45632 _45630 _45631) (@lem3927683 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927732 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term197 _45630 _45631 _45632 _45633.
Proof. exact (h1). Qed.
Lemma lem3927733 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term196 _45630 _45631 _45632 _45633.
Proof. exact (proj2 (@lem3927732 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927735 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term195 _45630 _45631 _45632 _45633.
Proof. exact (proj2 (@lem3927733 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927737 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term194 _45630 _45631 _45632 _45633.
Proof. exact (proj2 (@lem3927735 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927739 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term192 _45630 _45631 _45632 _45633.
Proof. exact (proj2 (@lem3927737 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927741 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term190 _45630 _45631 _45632 _45633.
Proof. exact (proj2 (@lem3927739 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927742 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term162 _45630 _45632 _45631 _45633.
Proof. exact (proj1 (@lem3927739 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927743 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term160 _45631 _45633.
Proof. exact (proj2 (@lem3927742 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927744 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term160 _45630 _45632.
Proof. exact (proj1 (@lem3927742 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927746 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3927747 : term198 = term199.
Proof. exact (@lem3927746 term92 term110). Qed.
Lemma lem3927749 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927750 : term110 = term174.
Proof. exact (@lem3927749 term20). Qed.
Lemma lem3927752 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927753 : term92 = term128.
Proof. exact (@lem3927752 (NUMERAL 0)). Qed.
Lemma lem3927754 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3927755 : term200 = term201.
Proof. exact (MK_COMB (@lem3927754) (@lem3927753)). Qed.
Lemma lem3927756 : term199 = term202.
Proof. exact (MK_COMB (@lem3927755) (@lem3927750)). Qed.
Lemma lem3927757 : term203.
Proof. exact (@lem1980255 term92 term110 term110 term110). Qed.
Lemma lem3927759 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927760 : term199 = term205.
Proof. exact (@lem3927759 (NUMERAL 0) term20). Qed.
Lemma lem3927761 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927762 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927763 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927762 h1) (fun h1 : term205 = True => @lem3927761)). Qed.
Lemma lem3927764 : term205 = True.
Proof. exact (EQ_MP (@lem3927763) (@lem3927761)). Qed.
Lemma lem3927765 : term199 = True.
Proof. exact (TRANS (@lem3927760) (@lem3927764)). Qed.
Lemma lem3927766 : True = term199.
Proof. exact (SYM (@lem3927765)). Qed.
Lemma lem3927767 : term199.
Proof. exact (EQ_MP (@lem3927766) (@lem0)). Qed.
Lemma lem3927768 : term207.
Proof. exact (@lem3927757 (@lem3927767)). Qed.
Lemma lem3927770 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927771 : term199 = term205.
Proof. exact (@lem3927770 (NUMERAL 0) term20). Qed.
Lemma lem3927772 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927773 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927774 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927773 h1) (fun h1 : term205 = True => @lem3927772)). Qed.
Lemma lem3927775 : term205 = True.
Proof. exact (EQ_MP (@lem3927774) (@lem3927772)). Qed.
Lemma lem3927776 : term199 = True.
Proof. exact (TRANS (@lem3927771) (@lem3927775)). Qed.
Lemma lem3927777 : True = term199.
Proof. exact (SYM (@lem3927776)). Qed.
Lemma lem3927778 : term199.
Proof. exact (EQ_MP (@lem3927777) (@lem0)). Qed.
Lemma lem3927779 : term202 = term208.
Proof. exact (@lem3927768 (@lem3927778)). Qed.
Lemma lem3927781 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927782 : term140 = term141.
Proof. exact (@lem3927781 term20 term20). Qed.
Lemma lem3927783 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927784 : term143 = term20.
Proof. exact (EQ_MP (@lem3927783) (@lem940073)). Qed.
Lemma lem3927785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927786 : term141 = term110.
Proof. exact (MK_COMB (@lem3927785) (@lem3927784)). Qed.
Lemma lem3927787 : term140 = term110.
Proof. exact (TRANS (@lem3927782) (@lem3927786)). Qed.
Lemma lem3927789 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3927790 : term210 = term92.
Proof. exact (@lem3927789 term20). Qed.
Lemma lem3927791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3927792 : term211 = term200.
Proof. exact (MK_COMB (@lem3927791) (@lem3927790)). Qed.
Lemma lem3927793 : term208 = term199.
Proof. exact (MK_COMB (@lem3927792) (@lem3927787)). Qed.
Lemma lem3927795 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927796 : term199 = term205.
Proof. exact (@lem3927795 (NUMERAL 0) term20). Qed.
Lemma lem3927797 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927798 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927799 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927798 h1) (fun h1 : term205 = True => @lem3927797)). Qed.
Lemma lem3927800 : term205 = True.
Proof. exact (EQ_MP (@lem3927799) (@lem3927797)). Qed.
Lemma lem3927801 : term199 = True.
Proof. exact (TRANS (@lem3927796) (@lem3927800)). Qed.
Lemma lem3927802 : term208 = True.
Proof. exact (TRANS (@lem3927793) (@lem3927801)). Qed.
Lemma lem3927803 : term202 = True.
Proof. exact (TRANS (@lem3927779) (@lem3927802)). Qed.
Lemma lem3927804 : term199 = True.
Proof. exact (TRANS (@lem3927756) (@lem3927803)). Qed.
Lemma lem3927805 : term198 = True.
Proof. exact (TRANS (@lem3927747) (@lem3927804)). Qed.
Lemma lem3927806 : True = term198.
Proof. exact (SYM (@lem3927805)). Qed.
Lemma lem3927807 : term198.
Proof. exact (EQ_MP (@lem3927806) (@lem0)). Qed.
Lemma lem3927808 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term212 _45630 _45631 _45632 _45633.
Proof. exact (conj (@lem3927807) (@lem3927741 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927810 (x : real) (y : real) : term213 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3927811 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : term214 _45630 _45631 _45632 _45633.
Proof. exact (@lem3927810 term110 (term187 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927812 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term215 _45630 _45631 _45632 _45633.
Proof. exact (@lem3927811 _45630 _45631 _45632 _45633 (@lem3927808 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927813 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term216 _45630 _45631 _45632 _45633) = (term187 _45630 _45631 _45632 _45633).
Proof. exact (@lem1982733 (term187 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927815 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term217 _45630 _45631 _45632 _45633) = (term189 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927814) (@lem3927813 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927816 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927817 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term215 _45630 _45631 _45632 _45633) = (term190 _45630 _45631 _45632 _45633).
Proof. exact (MK_COMB (@lem3927815 _45630 _45631 _45632 _45633) (@lem3927816)). Qed.
Lemma lem3927818 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term190 _45630 _45631 _45632 _45633.
Proof. exact (EQ_MP (@lem3927817 _45630 _45631 _45632 _45633) (@lem3927812 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927820 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3927821 : term198 = term199.
Proof. exact (@lem3927820 term92 term110). Qed.
Lemma lem3927823 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927824 : term110 = term174.
Proof. exact (@lem3927823 term20). Qed.
Lemma lem3927826 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927827 : term92 = term128.
Proof. exact (@lem3927826 (NUMERAL 0)). Qed.
Lemma lem3927828 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3927829 : term200 = term201.
Proof. exact (MK_COMB (@lem3927828) (@lem3927827)). Qed.
Lemma lem3927830 : term199 = term202.
Proof. exact (MK_COMB (@lem3927829) (@lem3927824)). Qed.
Lemma lem3927831 : term203.
Proof. exact (@lem1980255 term92 term110 term110 term110). Qed.
Lemma lem3927833 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927834 : term199 = term205.
Proof. exact (@lem3927833 (NUMERAL 0) term20). Qed.
Lemma lem3927835 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927836 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927837 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927836 h1) (fun h1 : term205 = True => @lem3927835)). Qed.
Lemma lem3927838 : term205 = True.
Proof. exact (EQ_MP (@lem3927837) (@lem3927835)). Qed.
Lemma lem3927839 : term199 = True.
Proof. exact (TRANS (@lem3927834) (@lem3927838)). Qed.
Lemma lem3927840 : True = term199.
Proof. exact (SYM (@lem3927839)). Qed.
Lemma lem3927841 : term199.
Proof. exact (EQ_MP (@lem3927840) (@lem0)). Qed.
Lemma lem3927842 : term207.
Proof. exact (@lem3927831 (@lem3927841)). Qed.
Lemma lem3927844 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927845 : term199 = term205.
Proof. exact (@lem3927844 (NUMERAL 0) term20). Qed.
Lemma lem3927846 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927847 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927848 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927847 h1) (fun h1 : term205 = True => @lem3927846)). Qed.
Lemma lem3927849 : term205 = True.
Proof. exact (EQ_MP (@lem3927848) (@lem3927846)). Qed.
Lemma lem3927850 : term199 = True.
Proof. exact (TRANS (@lem3927845) (@lem3927849)). Qed.
Lemma lem3927851 : True = term199.
Proof. exact (SYM (@lem3927850)). Qed.
Lemma lem3927852 : term199.
Proof. exact (EQ_MP (@lem3927851) (@lem0)). Qed.
Lemma lem3927853 : term202 = term208.
Proof. exact (@lem3927842 (@lem3927852)). Qed.
Lemma lem3927855 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927856 : term140 = term141.
Proof. exact (@lem3927855 term20 term20). Qed.
Lemma lem3927857 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927858 : term143 = term20.
Proof. exact (EQ_MP (@lem3927857) (@lem940073)). Qed.
Lemma lem3927859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927860 : term141 = term110.
Proof. exact (MK_COMB (@lem3927859) (@lem3927858)). Qed.
Lemma lem3927861 : term140 = term110.
Proof. exact (TRANS (@lem3927856) (@lem3927860)). Qed.
Lemma lem3927863 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3927864 : term210 = term92.
Proof. exact (@lem3927863 term20). Qed.
Lemma lem3927865 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3927866 : term211 = term200.
Proof. exact (MK_COMB (@lem3927865) (@lem3927864)). Qed.
Lemma lem3927867 : term208 = term199.
Proof. exact (MK_COMB (@lem3927866) (@lem3927861)). Qed.
Lemma lem3927869 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927870 : term199 = term205.
Proof. exact (@lem3927869 (NUMERAL 0) term20). Qed.
Lemma lem3927871 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927872 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927873 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927872 h1) (fun h1 : term205 = True => @lem3927871)). Qed.
Lemma lem3927874 : term205 = True.
Proof. exact (EQ_MP (@lem3927873) (@lem3927871)). Qed.
Lemma lem3927875 : term199 = True.
Proof. exact (TRANS (@lem3927870) (@lem3927874)). Qed.
Lemma lem3927876 : term208 = True.
Proof. exact (TRANS (@lem3927867) (@lem3927875)). Qed.
Lemma lem3927877 : term202 = True.
Proof. exact (TRANS (@lem3927853) (@lem3927876)). Qed.
Lemma lem3927878 : term199 = True.
Proof. exact (TRANS (@lem3927830) (@lem3927877)). Qed.
Lemma lem3927879 : term198 = True.
Proof. exact (TRANS (@lem3927821) (@lem3927878)). Qed.
Lemma lem3927880 : True = term198.
Proof. exact (SYM (@lem3927879)). Qed.
Lemma lem3927881 : term198.
Proof. exact (EQ_MP (@lem3927880) (@lem0)). Qed.
Lemma lem3927882 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term218 _45630 _45632.
Proof. exact (conj (@lem3927881) (@lem3927744 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927884 (x : real) (y : real) : term213 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3927885 (_45630 : int) (_45632 : int) : term219 _45630 _45632.
Proof. exact (@lem3927884 term110 (term156 _45630 _45632)). Qed.
Lemma lem3927886 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term220 _45630 _45632.
Proof. exact (@lem3927885 _45630 _45632 (@lem3927882 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927887 (_45630 : int) (_45632 : int) : (term221 _45630 _45632) = (term156 _45630 _45632).
Proof. exact (@lem1982733 (term156 _45630 _45632)). Qed.
Lemma lem3927888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3927889 (_45630 : int) (_45632 : int) : (term222 _45630 _45632) = (term159 _45630 _45632).
Proof. exact (MK_COMB (@lem3927888) (@lem3927887 _45630 _45632)). Qed.
Lemma lem3927890 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3927891 (_45630 : int) (_45632 : int) : (term220 _45630 _45632) = (term160 _45630 _45632).
Proof. exact (MK_COMB (@lem3927889 _45630 _45632) (@lem3927890)). Qed.
Lemma lem3927892 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term160 _45630 _45632.
Proof. exact (EQ_MP (@lem3927891 _45630 _45632) (@lem3927886 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927893 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term223 _45630 _45631 _45632 _45633.
Proof. exact (conj (@lem3927892 _45630 _45631 _45632 _45633 h1) (@lem3927818 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927895 (x : real) (y : real) : term224 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3927896 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : term225 _45630 _45631 _45632 _45633.
Proof. exact (@lem3927895 (term156 _45630 _45632) (term187 _45630 _45631 _45632 _45633)). Qed.
Lemma lem3927897 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term226 _45630 _45631 _45632 _45633.
Proof. exact (@lem3927896 _45630 _45631 _45632 _45633 (@lem3927893 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3927898 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) : (term227 _45630 _45631 _45632 _45633) = (term228 _45630 _45631 _45632 _45633).
Proof. exact (@lem1982753 (term157 _45630) (real_of_int _45630) (real_of_int _45632) (term229 _45631 _45632 _45633)). Qed.
Lemma lem3927899 (_45630 : int) : (term230 _45630) = (term231 _45630).
Proof. exact (@lem1982713 term131 (real_of_int _45630)). Qed.
Lemma lem3927901 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3927902 : term110 = term174.
Proof. exact (@lem3927901 term20). Qed.
Lemma lem3927904 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3927905 : term131 = term132.
Proof. exact (@lem3927904 term20). Qed.
Lemma lem3927906 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3927907 : term232 = term233.
Proof. exact (MK_COMB (@lem3927906) (@lem3927905)). Qed.
Lemma lem3927908 : term234 = term235.
Proof. exact (MK_COMB (@lem3927907) (@lem3927902)). Qed.
Lemma lem3927909 : term236.
Proof. exact (@lem1981473 term131 term110 term110 term110 term92 term110). Qed.
Lemma lem3927911 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927912 : term199 = term205.
Proof. exact (@lem3927911 (NUMERAL 0) term20). Qed.
Lemma lem3927913 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927914 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927915 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927914 h1) (fun h1 : term205 = True => @lem3927913)). Qed.
Lemma lem3927916 : term205 = True.
Proof. exact (EQ_MP (@lem3927915) (@lem3927913)). Qed.
Lemma lem3927917 : term199 = True.
Proof. exact (TRANS (@lem3927912) (@lem3927916)). Qed.
Lemma lem3927918 : True = term199.
Proof. exact (SYM (@lem3927917)). Qed.
Lemma lem3927919 : term199.
Proof. exact (EQ_MP (@lem3927918) (@lem0)). Qed.
Lemma lem3927920 : term237.
Proof. exact (@lem3927909 (@lem3927919)). Qed.
Lemma lem3927922 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927923 : term199 = term205.
Proof. exact (@lem3927922 (NUMERAL 0) term20). Qed.
Lemma lem3927924 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927925 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927926 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927925 h1) (fun h1 : term205 = True => @lem3927924)). Qed.
Lemma lem3927927 : term205 = True.
Proof. exact (EQ_MP (@lem3927926) (@lem3927924)). Qed.
Lemma lem3927928 : term199 = True.
Proof. exact (TRANS (@lem3927923) (@lem3927927)). Qed.
Lemma lem3927929 : True = term199.
Proof. exact (SYM (@lem3927928)). Qed.
Lemma lem3927930 : term199.
Proof. exact (EQ_MP (@lem3927929) (@lem0)). Qed.
Lemma lem3927931 : term238.
Proof. exact (@lem3927920 (@lem3927930)). Qed.
Lemma lem3927933 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3927934 : term199 = term205.
Proof. exact (@lem3927933 (NUMERAL 0) term20). Qed.
Lemma lem3927935 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3927936 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3927937 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3927936 h1) (fun h1 : term205 = True => @lem3927935)). Qed.
Lemma lem3927938 : term205 = True.
Proof. exact (EQ_MP (@lem3927937) (@lem3927935)). Qed.
Lemma lem3927939 : term199 = True.
Proof. exact (TRANS (@lem3927934) (@lem3927938)). Qed.
Lemma lem3927940 : True = term199.
Proof. exact (SYM (@lem3927939)). Qed.
Lemma lem3927941 : term199.
Proof. exact (EQ_MP (@lem3927940) (@lem0)). Qed.
Lemma lem3927942 : term239.
Proof. exact (@lem3927931 (@lem3927941)). Qed.
Lemma lem3927944 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927945 : term140 = term141.
Proof. exact (@lem3927944 term20 term20). Qed.
Lemma lem3927946 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927947 : term143 = term20.
Proof. exact (EQ_MP (@lem3927946) (@lem940073)). Qed.
Lemma lem3927948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927949 : term141 = term110.
Proof. exact (MK_COMB (@lem3927948) (@lem3927947)). Qed.
Lemma lem3927950 : term140 = term110.
Proof. exact (TRANS (@lem3927945) (@lem3927949)). Qed.
Lemma lem3927952 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3927953 : term175 = term180.
Proof. exact (@lem3927952 term20 term20). Qed.
Lemma lem3927954 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927955 : term143 = term20.
Proof. exact (EQ_MP (@lem3927954) (@lem940073)). Qed.
Lemma lem3927956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927957 : term141 = term110.
Proof. exact (MK_COMB (@lem3927956) (@lem3927955)). Qed.
Lemma lem3927958 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3927959 : term180 = term131.
Proof. exact (MK_COMB (@lem3927958) (@lem3927957)). Qed.
Lemma lem3927960 : term175 = term131.
Proof. exact (TRANS (@lem3927953) (@lem3927959)). Qed.
Lemma lem3927961 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3927962 : term240 = term232.
Proof. exact (MK_COMB (@lem3927961) (@lem3927960)). Qed.
Lemma lem3927963 : term241 = term234.
Proof. exact (MK_COMB (@lem3927962) (@lem3927950)). Qed.
Lemma lem3927965 (m : nat) : (term242 m) = term92.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3927966 : term234 = term92.
Proof. exact (@lem3927965 term20). Qed.
Lemma lem3927967 : term241 = term92.
Proof. exact (TRANS (@lem3927963) (@lem3927966)). Qed.
Lemma lem3927968 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927969 : term243 = term244.
Proof. exact (MK_COMB (@lem3927968) (@lem3927967)). Qed.
Lemma lem3927970 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem3927971 : term245 = term210.
Proof. exact (MK_COMB (@lem3927969) (@lem3927970)). Qed.
Lemma lem3927973 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3927974 : term210 = term92.
Proof. exact (@lem3927973 term20). Qed.
Lemma lem3927975 : term245 = term92.
Proof. exact (TRANS (@lem3927971) (@lem3927974)). Qed.
Lemma lem3927977 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3927978 : term140 = term141.
Proof. exact (@lem3927977 term20 term20). Qed.
Lemma lem3927979 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3927980 : term143 = term20.
Proof. exact (EQ_MP (@lem3927979) (@lem940073)). Qed.
Lemma lem3927981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3927982 : term141 = term110.
Proof. exact (MK_COMB (@lem3927981) (@lem3927980)). Qed.
Lemma lem3927983 : term140 = term110.
Proof. exact (TRANS (@lem3927978) (@lem3927982)). Qed.
Lemma lem3927984 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3927985 : term246 = term210.
Proof. exact (MK_COMB (@lem3927984) (@lem3927983)). Qed.
Lemma lem3927987 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3927988 : term210 = term92.
Proof. exact (@lem3927987 term20). Qed.
Lemma lem3927989 : term246 = term92.
Proof. exact (TRANS (@lem3927985) (@lem3927988)). Qed.
Lemma lem3927990 : term92 = term246.
Proof. exact (SYM (@lem3927989)). Qed.
Lemma lem3927991 : term245 = term246.
Proof. exact (TRANS (@lem3927975) (@lem3927990)). Qed.
Lemma lem3927992 : term235 = term128.
Proof. exact (@lem3927942 (@lem3927991)). Qed.
Lemma lem3927993 : term234 = term128.
Proof. exact (TRANS (@lem3927908) (@lem3927992)). Qed.
Lemma lem3927995 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3927996 : term128 = term92.
Proof. exact (@lem3927995 term92). Qed.
Lemma lem3927997 : term234 = term92.
Proof. exact (TRANS (@lem3927993) (@lem3927996)). Qed.
Lemma lem3927998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3927999 : term247 = term244.
Proof. exact (MK_COMB (@lem3927998) (@lem3927997)). Qed.
Lemma lem3928000 (_45630 : int) : (real_of_int _45630) = (real_of_int _45630).
Proof. exact (eq_refl (real_of_int _45630)). Qed.
Lemma lem3928001 (_45630 : int) : (term231 _45630) = (term248 _45630).
Proof. exact (MK_COMB (@lem3927999) (@lem3928000 _45630)). Qed.
Lemma lem3928002 (_45630 : int) : (term230 _45630) = (term248 _45630).
Proof. exact (TRANS (@lem3927899 _45630) (@lem3928001 _45630)). Qed.
Lemma lem3928003 (_45630 : int) : (term248 _45630) = term92.
Proof. exact (@lem1982719 (real_of_int _45630)). Qed.
Lemma lem3928004 (_45630 : int) : (term230 _45630) = term92.
Proof. exact (TRANS (@lem3928002 _45630) (@lem3928003 _45630)). Qed.
Lemma lem3928005 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928006 (_45630 : int) : (term249 _45630) = term250.
Proof. exact (MK_COMB (@lem3928005) (@lem3928004 _45630)). Qed.
Lemma lem3928007 (_45631 : int) (_45632 : int) (_45633 : int) : (term251 _45631 _45632 _45633) = (term252 _45631 _45632 _45633).
Proof. exact (@lem1982757 (real_of_int _45631) (real_of_int _45632) (term185 _45632 _45633)). Qed.
Lemma lem3928008 (_45632 : int) (_45633 : int) : (term253 _45632 _45633) = (term254 _45632 _45633).
Proof. exact (@lem1982763 (real_of_int _45632) (term157 _45632) (term184 _45633)). Qed.
Lemma lem3928009 (_45632 : int) : (term255 _45632) = (term231 _45632).
Proof. exact (@lem1982715 term131 (real_of_int _45632)). Qed.
Lemma lem3928011 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928012 : term110 = term174.
Proof. exact (@lem3928011 term20). Qed.
Lemma lem3928014 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3928015 : term131 = term132.
Proof. exact (@lem3928014 term20). Qed.
Lemma lem3928016 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928017 : term232 = term233.
Proof. exact (MK_COMB (@lem3928016) (@lem3928015)). Qed.
Lemma lem3928018 : term234 = term235.
Proof. exact (MK_COMB (@lem3928017) (@lem3928012)). Qed.
Lemma lem3928019 : term236.
Proof. exact (@lem1981473 term131 term110 term110 term110 term92 term110). Qed.
Lemma lem3928021 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928022 : term199 = term205.
Proof. exact (@lem3928021 (NUMERAL 0) term20). Qed.
Lemma lem3928023 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928024 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928025 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928024 h1) (fun h1 : term205 = True => @lem3928023)). Qed.
Lemma lem3928026 : term205 = True.
Proof. exact (EQ_MP (@lem3928025) (@lem3928023)). Qed.
Lemma lem3928027 : term199 = True.
Proof. exact (TRANS (@lem3928022) (@lem3928026)). Qed.
Lemma lem3928028 : True = term199.
Proof. exact (SYM (@lem3928027)). Qed.
Lemma lem3928029 : term199.
Proof. exact (EQ_MP (@lem3928028) (@lem0)). Qed.
Lemma lem3928030 : term237.
Proof. exact (@lem3928019 (@lem3928029)). Qed.
Lemma lem3928032 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928033 : term199 = term205.
Proof. exact (@lem3928032 (NUMERAL 0) term20). Qed.
Lemma lem3928034 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928035 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928036 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928035 h1) (fun h1 : term205 = True => @lem3928034)). Qed.
Lemma lem3928037 : term205 = True.
Proof. exact (EQ_MP (@lem3928036) (@lem3928034)). Qed.
Lemma lem3928038 : term199 = True.
Proof. exact (TRANS (@lem3928033) (@lem3928037)). Qed.
Lemma lem3928039 : True = term199.
Proof. exact (SYM (@lem3928038)). Qed.
Lemma lem3928040 : term199.
Proof. exact (EQ_MP (@lem3928039) (@lem0)). Qed.
Lemma lem3928041 : term238.
Proof. exact (@lem3928030 (@lem3928040)). Qed.
Lemma lem3928043 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928044 : term199 = term205.
Proof. exact (@lem3928043 (NUMERAL 0) term20). Qed.
Lemma lem3928045 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928046 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928047 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928046 h1) (fun h1 : term205 = True => @lem3928045)). Qed.
Lemma lem3928048 : term205 = True.
Proof. exact (EQ_MP (@lem3928047) (@lem3928045)). Qed.
Lemma lem3928049 : term199 = True.
Proof. exact (TRANS (@lem3928044) (@lem3928048)). Qed.
Lemma lem3928050 : True = term199.
Proof. exact (SYM (@lem3928049)). Qed.
Lemma lem3928051 : term199.
Proof. exact (EQ_MP (@lem3928050) (@lem0)). Qed.
Lemma lem3928052 : term239.
Proof. exact (@lem3928041 (@lem3928051)). Qed.
Lemma lem3928054 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928055 : term140 = term141.
Proof. exact (@lem3928054 term20 term20). Qed.
Lemma lem3928056 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928057 : term143 = term20.
Proof. exact (EQ_MP (@lem3928056) (@lem940073)). Qed.
Lemma lem3928058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928059 : term141 = term110.
Proof. exact (MK_COMB (@lem3928058) (@lem3928057)). Qed.
Lemma lem3928060 : term140 = term110.
Proof. exact (TRANS (@lem3928055) (@lem3928059)). Qed.
Lemma lem3928062 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3928063 : term175 = term180.
Proof. exact (@lem3928062 term20 term20). Qed.
Lemma lem3928064 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928065 : term143 = term20.
Proof. exact (EQ_MP (@lem3928064) (@lem940073)). Qed.
Lemma lem3928066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928067 : term141 = term110.
Proof. exact (MK_COMB (@lem3928066) (@lem3928065)). Qed.
Lemma lem3928068 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3928069 : term180 = term131.
Proof. exact (MK_COMB (@lem3928068) (@lem3928067)). Qed.
Lemma lem3928070 : term175 = term131.
Proof. exact (TRANS (@lem3928063) (@lem3928069)). Qed.
Lemma lem3928071 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928072 : term240 = term232.
Proof. exact (MK_COMB (@lem3928071) (@lem3928070)). Qed.
Lemma lem3928073 : term241 = term234.
Proof. exact (MK_COMB (@lem3928072) (@lem3928060)). Qed.
Lemma lem3928075 (m : nat) : (term242 m) = term92.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3928076 : term234 = term92.
Proof. exact (@lem3928075 term20). Qed.
Lemma lem3928077 : term241 = term92.
Proof. exact (TRANS (@lem3928073) (@lem3928076)). Qed.
Lemma lem3928078 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928079 : term243 = term244.
Proof. exact (MK_COMB (@lem3928078) (@lem3928077)). Qed.
Lemma lem3928080 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem3928081 : term245 = term210.
Proof. exact (MK_COMB (@lem3928079) (@lem3928080)). Qed.
Lemma lem3928083 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928084 : term210 = term92.
Proof. exact (@lem3928083 term20). Qed.
Lemma lem3928085 : term245 = term92.
Proof. exact (TRANS (@lem3928081) (@lem3928084)). Qed.
Lemma lem3928087 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928088 : term140 = term141.
Proof. exact (@lem3928087 term20 term20). Qed.
Lemma lem3928089 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928090 : term143 = term20.
Proof. exact (EQ_MP (@lem3928089) (@lem940073)). Qed.
Lemma lem3928091 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928092 : term141 = term110.
Proof. exact (MK_COMB (@lem3928091) (@lem3928090)). Qed.
Lemma lem3928093 : term140 = term110.
Proof. exact (TRANS (@lem3928088) (@lem3928092)). Qed.
Lemma lem3928094 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3928095 : term246 = term210.
Proof. exact (MK_COMB (@lem3928094) (@lem3928093)). Qed.
Lemma lem3928097 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928098 : term210 = term92.
Proof. exact (@lem3928097 term20). Qed.
Lemma lem3928099 : term246 = term92.
Proof. exact (TRANS (@lem3928095) (@lem3928098)). Qed.
Lemma lem3928100 : term92 = term246.
Proof. exact (SYM (@lem3928099)). Qed.
Lemma lem3928101 : term245 = term246.
Proof. exact (TRANS (@lem3928085) (@lem3928100)). Qed.
Lemma lem3928102 : term235 = term128.
Proof. exact (@lem3928052 (@lem3928101)). Qed.
Lemma lem3928103 : term234 = term128.
Proof. exact (TRANS (@lem3928018) (@lem3928102)). Qed.
Lemma lem3928105 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3928106 : term128 = term92.
Proof. exact (@lem3928105 term92). Qed.
Lemma lem3928107 : term234 = term92.
Proof. exact (TRANS (@lem3928103) (@lem3928106)). Qed.
Lemma lem3928108 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928109 : term247 = term244.
Proof. exact (MK_COMB (@lem3928108) (@lem3928107)). Qed.
Lemma lem3928110 (_45632 : int) : (real_of_int _45632) = (real_of_int _45632).
Proof. exact (eq_refl (real_of_int _45632)). Qed.
Lemma lem3928111 (_45632 : int) : (term231 _45632) = (term248 _45632).
Proof. exact (MK_COMB (@lem3928109) (@lem3928110 _45632)). Qed.
Lemma lem3928112 (_45632 : int) : (term255 _45632) = (term248 _45632).
Proof. exact (TRANS (@lem3928009 _45632) (@lem3928111 _45632)). Qed.
Lemma lem3928113 (_45632 : int) : (term248 _45632) = term92.
Proof. exact (@lem1982719 (real_of_int _45632)). Qed.
Lemma lem3928114 (_45632 : int) : (term255 _45632) = term92.
Proof. exact (TRANS (@lem3928112 _45632) (@lem3928113 _45632)). Qed.
Lemma lem3928115 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928116 (_45632 : int) : (term256 _45632) = term250.
Proof. exact (MK_COMB (@lem3928115) (@lem3928114 _45632)). Qed.
Lemma lem3928117 (_45633 : int) : (term184 _45633) = (term184 _45633).
Proof. exact (eq_refl (term184 _45633)). Qed.
Lemma lem3928118 (_45632 : int) (_45633 : int) : (term254 _45632 _45633) = (term257 _45633).
Proof. exact (MK_COMB (@lem3928116 _45632) (@lem3928117 _45633)). Qed.
Lemma lem3928119 (_45632 : int) (_45633 : int) : (term253 _45632 _45633) = (term257 _45633).
Proof. exact (TRANS (@lem3928008 _45632 _45633) (@lem3928118 _45632 _45633)). Qed.
Lemma lem3928120 (_45633 : int) : (term257 _45633) = (term184 _45633).
Proof. exact (@lem1982721 (term184 _45633)). Qed.
Lemma lem3928121 (_45632 : int) (_45633 : int) : (term253 _45632 _45633) = (term184 _45633).
Proof. exact (TRANS (@lem3928119 _45632 _45633) (@lem3928120 _45633)). Qed.
Lemma lem3928122 (_45631 : int) : (term148 _45631) = (term148 _45631).
Proof. exact (eq_refl (term148 _45631)). Qed.
Lemma lem3928123 (_45632 : int) (_45631 : int) (_45633 : int) : (term252 _45631 _45632 _45633) = (term258 _45631 _45633).
Proof. exact (MK_COMB (@lem3928122 _45631) (@lem3928121 _45632 _45633)). Qed.
Lemma lem3928124 (_45632 : int) (_45631 : int) (_45633 : int) : (term251 _45631 _45632 _45633) = (term258 _45631 _45633).
Proof. exact (TRANS (@lem3928007 _45631 _45632 _45633) (@lem3928123 _45632 _45631 _45633)). Qed.
Lemma lem3928125 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term228 _45630 _45631 _45632 _45633) = (term259 _45631 _45633).
Proof. exact (MK_COMB (@lem3928006 _45630) (@lem3928124 _45632 _45631 _45633)). Qed.
Lemma lem3928126 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term227 _45630 _45631 _45632 _45633) = (term259 _45631 _45633).
Proof. exact (TRANS (@lem3927898 _45630 _45631 _45632 _45633) (@lem3928125 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3928127 (_45631 : int) (_45633 : int) : (term259 _45631 _45633) = (term258 _45631 _45633).
Proof. exact (@lem1982721 (term258 _45631 _45633)). Qed.
Lemma lem3928128 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term227 _45630 _45631 _45632 _45633) = (term258 _45631 _45633).
Proof. exact (TRANS (@lem3928126 _45630 _45632 _45631 _45633) (@lem3928127 _45631 _45633)). Qed.
Lemma lem3928129 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3928130 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term260 _45630 _45631 _45632 _45633) = (term261 _45631 _45633).
Proof. exact (MK_COMB (@lem3928129) (@lem3928128 _45630 _45632 _45631 _45633)). Qed.
Lemma lem3928131 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3928132 (_45630 : int) (_45632 : int) (_45631 : int) (_45633 : int) : (term226 _45630 _45631 _45632 _45633) = (term262 _45631 _45633).
Proof. exact (MK_COMB (@lem3928130 _45630 _45632 _45631 _45633) (@lem3928131)). Qed.
Lemma lem3928133 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term262 _45631 _45633.
Proof. exact (EQ_MP (@lem3928132 _45630 _45632 _45631 _45633) (@lem3927897 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928135 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3928136 : term198 = term199.
Proof. exact (@lem3928135 term92 term110). Qed.
Lemma lem3928138 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928139 : term110 = term174.
Proof. exact (@lem3928138 term20). Qed.
Lemma lem3928141 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928142 : term92 = term128.
Proof. exact (@lem3928141 (NUMERAL 0)). Qed.
Lemma lem3928143 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3928144 : term200 = term201.
Proof. exact (MK_COMB (@lem3928143) (@lem3928142)). Qed.
Lemma lem3928145 : term199 = term202.
Proof. exact (MK_COMB (@lem3928144) (@lem3928139)). Qed.
Lemma lem3928146 : term203.
Proof. exact (@lem1980255 term92 term110 term110 term110). Qed.
Lemma lem3928148 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928149 : term199 = term205.
Proof. exact (@lem3928148 (NUMERAL 0) term20). Qed.
Lemma lem3928150 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928151 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928152 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928151 h1) (fun h1 : term205 = True => @lem3928150)). Qed.
Lemma lem3928153 : term205 = True.
Proof. exact (EQ_MP (@lem3928152) (@lem3928150)). Qed.
Lemma lem3928154 : term199 = True.
Proof. exact (TRANS (@lem3928149) (@lem3928153)). Qed.
Lemma lem3928155 : True = term199.
Proof. exact (SYM (@lem3928154)). Qed.
Lemma lem3928156 : term199.
Proof. exact (EQ_MP (@lem3928155) (@lem0)). Qed.
Lemma lem3928157 : term207.
Proof. exact (@lem3928146 (@lem3928156)). Qed.
Lemma lem3928159 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928160 : term199 = term205.
Proof. exact (@lem3928159 (NUMERAL 0) term20). Qed.
Lemma lem3928161 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928162 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928163 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928162 h1) (fun h1 : term205 = True => @lem3928161)). Qed.
Lemma lem3928164 : term205 = True.
Proof. exact (EQ_MP (@lem3928163) (@lem3928161)). Qed.
Lemma lem3928165 : term199 = True.
Proof. exact (TRANS (@lem3928160) (@lem3928164)). Qed.
Lemma lem3928166 : True = term199.
Proof. exact (SYM (@lem3928165)). Qed.
Lemma lem3928167 : term199.
Proof. exact (EQ_MP (@lem3928166) (@lem0)). Qed.
Lemma lem3928168 : term202 = term208.
Proof. exact (@lem3928157 (@lem3928167)). Qed.
Lemma lem3928170 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928171 : term140 = term141.
Proof. exact (@lem3928170 term20 term20). Qed.
Lemma lem3928172 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928173 : term143 = term20.
Proof. exact (EQ_MP (@lem3928172) (@lem940073)). Qed.
Lemma lem3928174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928175 : term141 = term110.
Proof. exact (MK_COMB (@lem3928174) (@lem3928173)). Qed.
Lemma lem3928176 : term140 = term110.
Proof. exact (TRANS (@lem3928171) (@lem3928175)). Qed.
Lemma lem3928178 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928179 : term210 = term92.
Proof. exact (@lem3928178 term20). Qed.
Lemma lem3928180 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3928181 : term211 = term200.
Proof. exact (MK_COMB (@lem3928180) (@lem3928179)). Qed.
Lemma lem3928182 : term208 = term199.
Proof. exact (MK_COMB (@lem3928181) (@lem3928176)). Qed.
Lemma lem3928184 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928185 : term199 = term205.
Proof. exact (@lem3928184 (NUMERAL 0) term20). Qed.
Lemma lem3928186 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928187 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928188 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928187 h1) (fun h1 : term205 = True => @lem3928186)). Qed.
Lemma lem3928189 : term205 = True.
Proof. exact (EQ_MP (@lem3928188) (@lem3928186)). Qed.
Lemma lem3928190 : term199 = True.
Proof. exact (TRANS (@lem3928185) (@lem3928189)). Qed.
Lemma lem3928191 : term208 = True.
Proof. exact (TRANS (@lem3928182) (@lem3928190)). Qed.
Lemma lem3928192 : term202 = True.
Proof. exact (TRANS (@lem3928168) (@lem3928191)). Qed.
Lemma lem3928193 : term199 = True.
Proof. exact (TRANS (@lem3928145) (@lem3928192)). Qed.
Lemma lem3928194 : term198 = True.
Proof. exact (TRANS (@lem3928136) (@lem3928193)). Qed.
Lemma lem3928195 : True = term198.
Proof. exact (SYM (@lem3928194)). Qed.
Lemma lem3928196 : term198.
Proof. exact (EQ_MP (@lem3928195) (@lem0)). Qed.
Lemma lem3928197 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term263 _45631 _45633.
Proof. exact (conj (@lem3928196) (@lem3928133 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928199 (x : real) (y : real) : term213 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3928200 (_45631 : int) (_45633 : int) : term264 _45631 _45633.
Proof. exact (@lem3928199 term110 (term258 _45631 _45633)). Qed.
Lemma lem3928201 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term265 _45631 _45633.
Proof. exact (@lem3928200 _45631 _45633 (@lem3928197 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928202 (_45631 : int) (_45633 : int) : (term266 _45631 _45633) = (term258 _45631 _45633).
Proof. exact (@lem1982733 (term258 _45631 _45633)). Qed.
Lemma lem3928203 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3928204 (_45631 : int) (_45633 : int) : (term267 _45631 _45633) = (term261 _45631 _45633).
Proof. exact (MK_COMB (@lem3928203) (@lem3928202 _45631 _45633)). Qed.
Lemma lem3928205 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3928206 (_45631 : int) (_45633 : int) : (term265 _45631 _45633) = (term262 _45631 _45633).
Proof. exact (MK_COMB (@lem3928204 _45631 _45633) (@lem3928205)). Qed.
Lemma lem3928207 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term262 _45631 _45633.
Proof. exact (EQ_MP (@lem3928206 _45631 _45633) (@lem3928201 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928209 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3928210 : term198 = term199.
Proof. exact (@lem3928209 term92 term110). Qed.
Lemma lem3928212 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928213 : term110 = term174.
Proof. exact (@lem3928212 term20). Qed.
Lemma lem3928215 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928216 : term92 = term128.
Proof. exact (@lem3928215 (NUMERAL 0)). Qed.
Lemma lem3928217 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3928218 : term200 = term201.
Proof. exact (MK_COMB (@lem3928217) (@lem3928216)). Qed.
Lemma lem3928219 : term199 = term202.
Proof. exact (MK_COMB (@lem3928218) (@lem3928213)). Qed.
Lemma lem3928220 : term203.
Proof. exact (@lem1980255 term92 term110 term110 term110). Qed.
Lemma lem3928222 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928223 : term199 = term205.
Proof. exact (@lem3928222 (NUMERAL 0) term20). Qed.
Lemma lem3928224 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928225 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928226 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928225 h1) (fun h1 : term205 = True => @lem3928224)). Qed.
Lemma lem3928227 : term205 = True.
Proof. exact (EQ_MP (@lem3928226) (@lem3928224)). Qed.
Lemma lem3928228 : term199 = True.
Proof. exact (TRANS (@lem3928223) (@lem3928227)). Qed.
Lemma lem3928229 : True = term199.
Proof. exact (SYM (@lem3928228)). Qed.
Lemma lem3928230 : term199.
Proof. exact (EQ_MP (@lem3928229) (@lem0)). Qed.
Lemma lem3928231 : term207.
Proof. exact (@lem3928220 (@lem3928230)). Qed.
Lemma lem3928233 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928234 : term199 = term205.
Proof. exact (@lem3928233 (NUMERAL 0) term20). Qed.
Lemma lem3928235 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928236 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928237 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928236 h1) (fun h1 : term205 = True => @lem3928235)). Qed.
Lemma lem3928238 : term205 = True.
Proof. exact (EQ_MP (@lem3928237) (@lem3928235)). Qed.
Lemma lem3928239 : term199 = True.
Proof. exact (TRANS (@lem3928234) (@lem3928238)). Qed.
Lemma lem3928240 : True = term199.
Proof. exact (SYM (@lem3928239)). Qed.
Lemma lem3928241 : term199.
Proof. exact (EQ_MP (@lem3928240) (@lem0)). Qed.
Lemma lem3928242 : term202 = term208.
Proof. exact (@lem3928231 (@lem3928241)). Qed.
Lemma lem3928244 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928245 : term140 = term141.
Proof. exact (@lem3928244 term20 term20). Qed.
Lemma lem3928246 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928247 : term143 = term20.
Proof. exact (EQ_MP (@lem3928246) (@lem940073)). Qed.
Lemma lem3928248 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928249 : term141 = term110.
Proof. exact (MK_COMB (@lem3928248) (@lem3928247)). Qed.
Lemma lem3928250 : term140 = term110.
Proof. exact (TRANS (@lem3928245) (@lem3928249)). Qed.
Lemma lem3928252 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928253 : term210 = term92.
Proof. exact (@lem3928252 term20). Qed.
Lemma lem3928254 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3928255 : term211 = term200.
Proof. exact (MK_COMB (@lem3928254) (@lem3928253)). Qed.
Lemma lem3928256 : term208 = term199.
Proof. exact (MK_COMB (@lem3928255) (@lem3928250)). Qed.
Lemma lem3928258 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928259 : term199 = term205.
Proof. exact (@lem3928258 (NUMERAL 0) term20). Qed.
Lemma lem3928260 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928261 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928262 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928261 h1) (fun h1 : term205 = True => @lem3928260)). Qed.
Lemma lem3928263 : term205 = True.
Proof. exact (EQ_MP (@lem3928262) (@lem3928260)). Qed.
Lemma lem3928264 : term199 = True.
Proof. exact (TRANS (@lem3928259) (@lem3928263)). Qed.
Lemma lem3928265 : term208 = True.
Proof. exact (TRANS (@lem3928256) (@lem3928264)). Qed.
Lemma lem3928266 : term202 = True.
Proof. exact (TRANS (@lem3928242) (@lem3928265)). Qed.
Lemma lem3928267 : term199 = True.
Proof. exact (TRANS (@lem3928219) (@lem3928266)). Qed.
Lemma lem3928268 : term198 = True.
Proof. exact (TRANS (@lem3928210) (@lem3928267)). Qed.
Lemma lem3928269 : True = term198.
Proof. exact (SYM (@lem3928268)). Qed.
Lemma lem3928270 : term198.
Proof. exact (EQ_MP (@lem3928269) (@lem0)). Qed.
Lemma lem3928271 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term218 _45631 _45633.
Proof. exact (conj (@lem3928270) (@lem3927743 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928273 (x : real) (y : real) : term213 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3928274 (_45631 : int) (_45633 : int) : term219 _45631 _45633.
Proof. exact (@lem3928273 term110 (term156 _45631 _45633)). Qed.
Lemma lem3928275 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term220 _45631 _45633.
Proof. exact (@lem3928274 _45631 _45633 (@lem3928271 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928276 (_45631 : int) (_45633 : int) : (term221 _45631 _45633) = (term156 _45631 _45633).
Proof. exact (@lem1982733 (term156 _45631 _45633)). Qed.
Lemma lem3928277 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3928278 (_45631 : int) (_45633 : int) : (term222 _45631 _45633) = (term159 _45631 _45633).
Proof. exact (MK_COMB (@lem3928277) (@lem3928276 _45631 _45633)). Qed.
Lemma lem3928279 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3928280 (_45631 : int) (_45633 : int) : (term220 _45631 _45633) = (term160 _45631 _45633).
Proof. exact (MK_COMB (@lem3928278 _45631 _45633) (@lem3928279)). Qed.
Lemma lem3928281 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term160 _45631 _45633.
Proof. exact (EQ_MP (@lem3928280 _45631 _45633) (@lem3928275 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928282 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term268 _45631 _45633.
Proof. exact (conj (@lem3928281 _45630 _45631 _45632 _45633 h1) (@lem3928207 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928284 (x : real) (y : real) : term224 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3928285 (_45631 : int) (_45633 : int) : term269 _45631 _45633.
Proof. exact (@lem3928284 (term156 _45631 _45633) (term258 _45631 _45633)). Qed.
Lemma lem3928286 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term270 _45631 _45633.
Proof. exact (@lem3928285 _45631 _45633 (@lem3928282 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928287 (_45631 : int) (_45633 : int) : (term271 _45631 _45633) = (term272 _45631 _45633).
Proof. exact (@lem1982753 (term157 _45631) (real_of_int _45631) (real_of_int _45633) (term184 _45633)). Qed.
Lemma lem3928288 (_45631 : int) : (term230 _45631) = (term231 _45631).
Proof. exact (@lem1982713 term131 (real_of_int _45631)). Qed.
Lemma lem3928290 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928291 : term110 = term174.
Proof. exact (@lem3928290 term20). Qed.
Lemma lem3928293 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3928294 : term131 = term132.
Proof. exact (@lem3928293 term20). Qed.
Lemma lem3928295 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928296 : term232 = term233.
Proof. exact (MK_COMB (@lem3928295) (@lem3928294)). Qed.
Lemma lem3928297 : term234 = term235.
Proof. exact (MK_COMB (@lem3928296) (@lem3928291)). Qed.
Lemma lem3928298 : term236.
Proof. exact (@lem1981473 term131 term110 term110 term110 term92 term110). Qed.
Lemma lem3928300 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928301 : term199 = term205.
Proof. exact (@lem3928300 (NUMERAL 0) term20). Qed.
Lemma lem3928302 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928303 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928304 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928303 h1) (fun h1 : term205 = True => @lem3928302)). Qed.
Lemma lem3928305 : term205 = True.
Proof. exact (EQ_MP (@lem3928304) (@lem3928302)). Qed.
Lemma lem3928306 : term199 = True.
Proof. exact (TRANS (@lem3928301) (@lem3928305)). Qed.
Lemma lem3928307 : True = term199.
Proof. exact (SYM (@lem3928306)). Qed.
Lemma lem3928308 : term199.
Proof. exact (EQ_MP (@lem3928307) (@lem0)). Qed.
Lemma lem3928309 : term237.
Proof. exact (@lem3928298 (@lem3928308)). Qed.
Lemma lem3928311 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928312 : term199 = term205.
Proof. exact (@lem3928311 (NUMERAL 0) term20). Qed.
Lemma lem3928313 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928314 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928315 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928314 h1) (fun h1 : term205 = True => @lem3928313)). Qed.
Lemma lem3928316 : term205 = True.
Proof. exact (EQ_MP (@lem3928315) (@lem3928313)). Qed.
Lemma lem3928317 : term199 = True.
Proof. exact (TRANS (@lem3928312) (@lem3928316)). Qed.
Lemma lem3928318 : True = term199.
Proof. exact (SYM (@lem3928317)). Qed.
Lemma lem3928319 : term199.
Proof. exact (EQ_MP (@lem3928318) (@lem0)). Qed.
Lemma lem3928320 : term238.
Proof. exact (@lem3928309 (@lem3928319)). Qed.
Lemma lem3928322 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928323 : term199 = term205.
Proof. exact (@lem3928322 (NUMERAL 0) term20). Qed.
Lemma lem3928324 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928325 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928326 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928325 h1) (fun h1 : term205 = True => @lem3928324)). Qed.
Lemma lem3928327 : term205 = True.
Proof. exact (EQ_MP (@lem3928326) (@lem3928324)). Qed.
Lemma lem3928328 : term199 = True.
Proof. exact (TRANS (@lem3928323) (@lem3928327)). Qed.
Lemma lem3928329 : True = term199.
Proof. exact (SYM (@lem3928328)). Qed.
Lemma lem3928330 : term199.
Proof. exact (EQ_MP (@lem3928329) (@lem0)). Qed.
Lemma lem3928331 : term239.
Proof. exact (@lem3928320 (@lem3928330)). Qed.
Lemma lem3928333 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928334 : term140 = term141.
Proof. exact (@lem3928333 term20 term20). Qed.
Lemma lem3928335 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928336 : term143 = term20.
Proof. exact (EQ_MP (@lem3928335) (@lem940073)). Qed.
Lemma lem3928337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928338 : term141 = term110.
Proof. exact (MK_COMB (@lem3928337) (@lem3928336)). Qed.
Lemma lem3928339 : term140 = term110.
Proof. exact (TRANS (@lem3928334) (@lem3928338)). Qed.
Lemma lem3928341 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3928342 : term175 = term180.
Proof. exact (@lem3928341 term20 term20). Qed.
Lemma lem3928343 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928344 : term143 = term20.
Proof. exact (EQ_MP (@lem3928343) (@lem940073)). Qed.
Lemma lem3928345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928346 : term141 = term110.
Proof. exact (MK_COMB (@lem3928345) (@lem3928344)). Qed.
Lemma lem3928347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3928348 : term180 = term131.
Proof. exact (MK_COMB (@lem3928347) (@lem3928346)). Qed.
Lemma lem3928349 : term175 = term131.
Proof. exact (TRANS (@lem3928342) (@lem3928348)). Qed.
Lemma lem3928350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928351 : term240 = term232.
Proof. exact (MK_COMB (@lem3928350) (@lem3928349)). Qed.
Lemma lem3928352 : term241 = term234.
Proof. exact (MK_COMB (@lem3928351) (@lem3928339)). Qed.
Lemma lem3928354 (m : nat) : (term242 m) = term92.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3928355 : term234 = term92.
Proof. exact (@lem3928354 term20). Qed.
Lemma lem3928356 : term241 = term92.
Proof. exact (TRANS (@lem3928352) (@lem3928355)). Qed.
Lemma lem3928357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928358 : term243 = term244.
Proof. exact (MK_COMB (@lem3928357) (@lem3928356)). Qed.
Lemma lem3928359 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem3928360 : term245 = term210.
Proof. exact (MK_COMB (@lem3928358) (@lem3928359)). Qed.
Lemma lem3928362 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928363 : term210 = term92.
Proof. exact (@lem3928362 term20). Qed.
Lemma lem3928364 : term245 = term92.
Proof. exact (TRANS (@lem3928360) (@lem3928363)). Qed.
Lemma lem3928366 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928367 : term140 = term141.
Proof. exact (@lem3928366 term20 term20). Qed.
Lemma lem3928368 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928369 : term143 = term20.
Proof. exact (EQ_MP (@lem3928368) (@lem940073)). Qed.
Lemma lem3928370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928371 : term141 = term110.
Proof. exact (MK_COMB (@lem3928370) (@lem3928369)). Qed.
Lemma lem3928372 : term140 = term110.
Proof. exact (TRANS (@lem3928367) (@lem3928371)). Qed.
Lemma lem3928373 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3928374 : term246 = term210.
Proof. exact (MK_COMB (@lem3928373) (@lem3928372)). Qed.
Lemma lem3928376 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928377 : term210 = term92.
Proof. exact (@lem3928376 term20). Qed.
Lemma lem3928378 : term246 = term92.
Proof. exact (TRANS (@lem3928374) (@lem3928377)). Qed.
Lemma lem3928379 : term92 = term246.
Proof. exact (SYM (@lem3928378)). Qed.
Lemma lem3928380 : term245 = term246.
Proof. exact (TRANS (@lem3928364) (@lem3928379)). Qed.
Lemma lem3928381 : term235 = term128.
Proof. exact (@lem3928331 (@lem3928380)). Qed.
Lemma lem3928382 : term234 = term128.
Proof. exact (TRANS (@lem3928297) (@lem3928381)). Qed.
Lemma lem3928384 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3928385 : term128 = term92.
Proof. exact (@lem3928384 term92). Qed.
Lemma lem3928386 : term234 = term92.
Proof. exact (TRANS (@lem3928382) (@lem3928385)). Qed.
Lemma lem3928387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928388 : term247 = term244.
Proof. exact (MK_COMB (@lem3928387) (@lem3928386)). Qed.
Lemma lem3928389 (_45631 : int) : (real_of_int _45631) = (real_of_int _45631).
Proof. exact (eq_refl (real_of_int _45631)). Qed.
Lemma lem3928390 (_45631 : int) : (term231 _45631) = (term248 _45631).
Proof. exact (MK_COMB (@lem3928388) (@lem3928389 _45631)). Qed.
Lemma lem3928391 (_45631 : int) : (term230 _45631) = (term248 _45631).
Proof. exact (TRANS (@lem3928288 _45631) (@lem3928390 _45631)). Qed.
Lemma lem3928392 (_45631 : int) : (term248 _45631) = term92.
Proof. exact (@lem1982719 (real_of_int _45631)). Qed.
Lemma lem3928393 (_45631 : int) : (term230 _45631) = term92.
Proof. exact (TRANS (@lem3928391 _45631) (@lem3928392 _45631)). Qed.
Lemma lem3928394 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928395 (_45631 : int) : (term249 _45631) = term250.
Proof. exact (MK_COMB (@lem3928394) (@lem3928393 _45631)). Qed.
Lemma lem3928396 (_45633 : int) : (term273 _45633) = (term274 _45633).
Proof. exact (@lem1982763 (real_of_int _45633) (term157 _45633) term131). Qed.
Lemma lem3928397 (_45633 : int) : (term255 _45633) = (term231 _45633).
Proof. exact (@lem1982715 term131 (real_of_int _45633)). Qed.
Lemma lem3928399 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928400 : term110 = term174.
Proof. exact (@lem3928399 term20). Qed.
Lemma lem3928402 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3928403 : term131 = term132.
Proof. exact (@lem3928402 term20). Qed.
Lemma lem3928404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928405 : term232 = term233.
Proof. exact (MK_COMB (@lem3928404) (@lem3928403)). Qed.
Lemma lem3928406 : term234 = term235.
Proof. exact (MK_COMB (@lem3928405) (@lem3928400)). Qed.
Lemma lem3928407 : term236.
Proof. exact (@lem1981473 term131 term110 term110 term110 term92 term110). Qed.
Lemma lem3928409 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928410 : term199 = term205.
Proof. exact (@lem3928409 (NUMERAL 0) term20). Qed.
Lemma lem3928411 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928412 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928413 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928412 h1) (fun h1 : term205 = True => @lem3928411)). Qed.
Lemma lem3928414 : term205 = True.
Proof. exact (EQ_MP (@lem3928413) (@lem3928411)). Qed.
Lemma lem3928415 : term199 = True.
Proof. exact (TRANS (@lem3928410) (@lem3928414)). Qed.
Lemma lem3928416 : True = term199.
Proof. exact (SYM (@lem3928415)). Qed.
Lemma lem3928417 : term199.
Proof. exact (EQ_MP (@lem3928416) (@lem0)). Qed.
Lemma lem3928418 : term237.
Proof. exact (@lem3928407 (@lem3928417)). Qed.
Lemma lem3928420 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928421 : term199 = term205.
Proof. exact (@lem3928420 (NUMERAL 0) term20). Qed.
Lemma lem3928422 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928423 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928424 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928423 h1) (fun h1 : term205 = True => @lem3928422)). Qed.
Lemma lem3928425 : term205 = True.
Proof. exact (EQ_MP (@lem3928424) (@lem3928422)). Qed.
Lemma lem3928426 : term199 = True.
Proof. exact (TRANS (@lem3928421) (@lem3928425)). Qed.
Lemma lem3928427 : True = term199.
Proof. exact (SYM (@lem3928426)). Qed.
Lemma lem3928428 : term199.
Proof. exact (EQ_MP (@lem3928427) (@lem0)). Qed.
Lemma lem3928429 : term238.
Proof. exact (@lem3928418 (@lem3928428)). Qed.
Lemma lem3928431 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928432 : term199 = term205.
Proof. exact (@lem3928431 (NUMERAL 0) term20). Qed.
Lemma lem3928433 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928434 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928435 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928434 h1) (fun h1 : term205 = True => @lem3928433)). Qed.
Lemma lem3928436 : term205 = True.
Proof. exact (EQ_MP (@lem3928435) (@lem3928433)). Qed.
Lemma lem3928437 : term199 = True.
Proof. exact (TRANS (@lem3928432) (@lem3928436)). Qed.
Lemma lem3928438 : True = term199.
Proof. exact (SYM (@lem3928437)). Qed.
Lemma lem3928439 : term199.
Proof. exact (EQ_MP (@lem3928438) (@lem0)). Qed.
Lemma lem3928440 : term239.
Proof. exact (@lem3928429 (@lem3928439)). Qed.
Lemma lem3928442 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928443 : term140 = term141.
Proof. exact (@lem3928442 term20 term20). Qed.
Lemma lem3928444 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928445 : term143 = term20.
Proof. exact (EQ_MP (@lem3928444) (@lem940073)). Qed.
Lemma lem3928446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928447 : term141 = term110.
Proof. exact (MK_COMB (@lem3928446) (@lem3928445)). Qed.
Lemma lem3928448 : term140 = term110.
Proof. exact (TRANS (@lem3928443) (@lem3928447)). Qed.
Lemma lem3928450 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3928451 : term175 = term180.
Proof. exact (@lem3928450 term20 term20). Qed.
Lemma lem3928452 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928453 : term143 = term20.
Proof. exact (EQ_MP (@lem3928452) (@lem940073)). Qed.
Lemma lem3928454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928455 : term141 = term110.
Proof. exact (MK_COMB (@lem3928454) (@lem3928453)). Qed.
Lemma lem3928456 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3928457 : term180 = term131.
Proof. exact (MK_COMB (@lem3928456) (@lem3928455)). Qed.
Lemma lem3928458 : term175 = term131.
Proof. exact (TRANS (@lem3928451) (@lem3928457)). Qed.
Lemma lem3928459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928460 : term240 = term232.
Proof. exact (MK_COMB (@lem3928459) (@lem3928458)). Qed.
Lemma lem3928461 : term241 = term234.
Proof. exact (MK_COMB (@lem3928460) (@lem3928448)). Qed.
Lemma lem3928463 (m : nat) : (term242 m) = term92.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3928464 : term234 = term92.
Proof. exact (@lem3928463 term20). Qed.
Lemma lem3928465 : term241 = term92.
Proof. exact (TRANS (@lem3928461) (@lem3928464)). Qed.
Lemma lem3928466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928467 : term243 = term244.
Proof. exact (MK_COMB (@lem3928466) (@lem3928465)). Qed.
Lemma lem3928468 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem3928469 : term245 = term210.
Proof. exact (MK_COMB (@lem3928467) (@lem3928468)). Qed.
Lemma lem3928471 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928472 : term210 = term92.
Proof. exact (@lem3928471 term20). Qed.
Lemma lem3928473 : term245 = term92.
Proof. exact (TRANS (@lem3928469) (@lem3928472)). Qed.
Lemma lem3928475 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3928476 : term140 = term141.
Proof. exact (@lem3928475 term20 term20). Qed.
Lemma lem3928477 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928478 : term143 = term20.
Proof. exact (EQ_MP (@lem3928477) (@lem940073)). Qed.
Lemma lem3928479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928480 : term141 = term110.
Proof. exact (MK_COMB (@lem3928479) (@lem3928478)). Qed.
Lemma lem3928481 : term140 = term110.
Proof. exact (TRANS (@lem3928476) (@lem3928480)). Qed.
Lemma lem3928482 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3928483 : term246 = term210.
Proof. exact (MK_COMB (@lem3928482) (@lem3928481)). Qed.
Lemma lem3928485 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928486 : term210 = term92.
Proof. exact (@lem3928485 term20). Qed.
Lemma lem3928487 : term246 = term92.
Proof. exact (TRANS (@lem3928483) (@lem3928486)). Qed.
Lemma lem3928488 : term92 = term246.
Proof. exact (SYM (@lem3928487)). Qed.
Lemma lem3928489 : term245 = term246.
Proof. exact (TRANS (@lem3928473) (@lem3928488)). Qed.
Lemma lem3928490 : term235 = term128.
Proof. exact (@lem3928440 (@lem3928489)). Qed.
Lemma lem3928491 : term234 = term128.
Proof. exact (TRANS (@lem3928406) (@lem3928490)). Qed.
Lemma lem3928493 (x : real) : (term147 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3928494 : term128 = term92.
Proof. exact (@lem3928493 term92). Qed.
Lemma lem3928495 : term234 = term92.
Proof. exact (TRANS (@lem3928491) (@lem3928494)). Qed.
Lemma lem3928496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3928497 : term247 = term244.
Proof. exact (MK_COMB (@lem3928496) (@lem3928495)). Qed.
Lemma lem3928498 (_45633 : int) : (real_of_int _45633) = (real_of_int _45633).
Proof. exact (eq_refl (real_of_int _45633)). Qed.
Lemma lem3928499 (_45633 : int) : (term231 _45633) = (term248 _45633).
Proof. exact (MK_COMB (@lem3928497) (@lem3928498 _45633)). Qed.
Lemma lem3928500 (_45633 : int) : (term255 _45633) = (term248 _45633).
Proof. exact (TRANS (@lem3928397 _45633) (@lem3928499 _45633)). Qed.
Lemma lem3928501 (_45633 : int) : (term248 _45633) = term92.
Proof. exact (@lem1982719 (real_of_int _45633)). Qed.
Lemma lem3928502 (_45633 : int) : (term255 _45633) = term92.
Proof. exact (TRANS (@lem3928500 _45633) (@lem3928501 _45633)). Qed.
Lemma lem3928503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3928504 (_45633 : int) : (term256 _45633) = term250.
Proof. exact (MK_COMB (@lem3928503) (@lem3928502 _45633)). Qed.
Lemma lem3928505 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem3928506 (_45633 : int) : (term274 _45633) = term275.
Proof. exact (MK_COMB (@lem3928504 _45633) (@lem3928505)). Qed.
Lemma lem3928507 (_45633 : int) : (term273 _45633) = term275.
Proof. exact (TRANS (@lem3928396 _45633) (@lem3928506 _45633)). Qed.
Lemma lem3928508 : term275 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem3928509 (_45633 : int) : (term273 _45633) = term131.
Proof. exact (TRANS (@lem3928507 _45633) (@lem3928508)). Qed.
Lemma lem3928510 (_45631 : int) (_45633 : int) : (term272 _45631 _45633) = term275.
Proof. exact (MK_COMB (@lem3928395 _45631) (@lem3928509 _45633)). Qed.
Lemma lem3928511 (_45631 : int) (_45633 : int) : (term271 _45631 _45633) = term275.
Proof. exact (TRANS (@lem3928287 _45631 _45633) (@lem3928510 _45631 _45633)). Qed.
Lemma lem3928512 : term275 = term131.
Proof. exact (@lem1982721 term131). Qed.
Lemma lem3928513 (_45631 : int) (_45633 : int) : (term271 _45631 _45633) = term131.
Proof. exact (TRANS (@lem3928511 _45631 _45633) (@lem3928512)). Qed.
Lemma lem3928514 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3928515 (_45631 : int) (_45633 : int) : (term276 _45631 _45633) = term277.
Proof. exact (MK_COMB (@lem3928514) (@lem3928513 _45631 _45633)). Qed.
Lemma lem3928516 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem3928517 (_45631 : int) (_45633 : int) : (term270 _45631 _45633) = term278.
Proof. exact (MK_COMB (@lem3928515 _45631 _45633) (@lem3928516)). Qed.
Lemma lem3928518 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term278.
Proof. exact (EQ_MP (@lem3928517 _45631 _45633) (@lem3928286 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928520 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3928521 : term278 = term279.
Proof. exact (@lem3928520 term92 term131). Qed.
Lemma lem3928523 (x : nat) : (term129 x) = (term130 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3928524 : term131 = term132.
Proof. exact (@lem3928523 term20). Qed.
Lemma lem3928526 (x : nat) : (real_of_num x) = (term127 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3928527 : term92 = term128.
Proof. exact (@lem3928526 (NUMERAL 0)). Qed.
Lemma lem3928528 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3928529 : term94 = term280.
Proof. exact (MK_COMB (@lem3928528) (@lem3928527)). Qed.
Lemma lem3928530 : term279 = term281.
Proof. exact (MK_COMB (@lem3928529) (@lem3928524)). Qed.
Lemma lem3928531 : term282.
Proof. exact (@lem1980026 term92 term110 term131 term110). Qed.
Lemma lem3928533 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928534 : term199 = term205.
Proof. exact (@lem3928533 (NUMERAL 0) term20). Qed.
Lemma lem3928535 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928536 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928537 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928536 h1) (fun h1 : term205 = True => @lem3928535)). Qed.
Lemma lem3928538 : term205 = True.
Proof. exact (EQ_MP (@lem3928537) (@lem3928535)). Qed.
Lemma lem3928539 : term199 = True.
Proof. exact (TRANS (@lem3928534) (@lem3928538)). Qed.
Lemma lem3928540 : True = term199.
Proof. exact (SYM (@lem3928539)). Qed.
Lemma lem3928541 : term199.
Proof. exact (EQ_MP (@lem3928540) (@lem0)). Qed.
Lemma lem3928542 : term283.
Proof. exact (@lem3928531 (@lem3928541)). Qed.
Lemma lem3928544 (m : nat) (n : nat) : (term204 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3928545 : term199 = term205.
Proof. exact (@lem3928544 (NUMERAL 0) term20). Qed.
Lemma lem3928546 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928547 (h1 : term206 = (BIT1 0)) : term205 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3928548 : (term206 = (BIT1 0)) = (term205 = True).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928547 h1) (fun h1 : term205 = True => @lem3928546)). Qed.
Lemma lem3928549 : term205 = True.
Proof. exact (EQ_MP (@lem3928548) (@lem3928546)). Qed.
Lemma lem3928550 : term199 = True.
Proof. exact (TRANS (@lem3928545) (@lem3928549)). Qed.
Lemma lem3928551 : True = term199.
Proof. exact (SYM (@lem3928550)). Qed.
Lemma lem3928552 : term199.
Proof. exact (EQ_MP (@lem3928551) (@lem0)). Qed.
Lemma lem3928553 : term281 = term284.
Proof. exact (@lem3928542 (@lem3928552)). Qed.
Lemma lem3928555 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3928556 : term175 = term180.
Proof. exact (@lem3928555 term20 term20). Qed.
Lemma lem3928557 : (term142 = (BIT1 0)) = (term143 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3928558 : term143 = term20.
Proof. exact (EQ_MP (@lem3928557) (@lem940073)). Qed.
Lemma lem3928559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3928560 : term141 = term110.
Proof. exact (MK_COMB (@lem3928559) (@lem3928558)). Qed.
Lemma lem3928561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3928562 : term180 = term131.
Proof. exact (MK_COMB (@lem3928561) (@lem3928560)). Qed.
Lemma lem3928563 : term175 = term131.
Proof. exact (TRANS (@lem3928556) (@lem3928562)). Qed.
Lemma lem3928565 (x : nat) : (term209 x) = term92.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3928566 : term210 = term92.
Proof. exact (@lem3928565 term20). Qed.
Lemma lem3928567 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3928568 : term285 = term94.
Proof. exact (MK_COMB (@lem3928567) (@lem3928566)). Qed.
Lemma lem3928569 : term284 = term279.
Proof. exact (MK_COMB (@lem3928568) (@lem3928563)). Qed.
Lemma lem3928571 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3928572 : term279 = term288.
Proof. exact (@lem3928571 (NUMERAL 0) term20). Qed.
Lemma lem3928573 : term206 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3928574 (h1 : term206 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3928575 : (term206 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term206 = (BIT1 0) => @lem3928574 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem3928573)). Qed.
Lemma lem3928576 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3928575) (@lem3928573)). Qed.
Lemma lem3928577 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3928578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3928579 : term289 = (and True).
Proof. exact (MK_COMB (@lem3928578) (@lem3928577)). Qed.
Lemma lem3928580 : term288 = (True /\ False).
Proof. exact (MK_COMB (@lem3928579) (@lem3928576)). Qed.
Lemma lem3928582 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3928583 : term288 = False.
Proof. exact (TRANS (@lem3928580) (@lem3928582)). Qed.
Lemma lem3928584 : term279 = False.
Proof. exact (TRANS (@lem3928572) (@lem3928583)). Qed.
Lemma lem3928585 : term284 = False.
Proof. exact (TRANS (@lem3928569) (@lem3928584)). Qed.
Lemma lem3928586 : term281 = False.
Proof. exact (TRANS (@lem3928553) (@lem3928585)). Qed.
Lemma lem3928587 : term279 = False.
Proof. exact (TRANS (@lem3928530) (@lem3928586)). Qed.
Lemma lem3928588 : term278 = False.
Proof. exact (TRANS (@lem3928521) (@lem3928587)). Qed.
Lemma lem3928589 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : False.
Proof. exact (EQ_MP (@lem3928588) (@lem3928518 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928591 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : term197 _45630 _45631 _45632 _45633.
Proof. exact (h1). Qed.
Lemma lem3928592 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : (term197 _45630 _45631 _45632 _45633) = False.
Proof. exact (prop_ext (fun h2 : term197 _45630 _45631 _45632 _45633 => @lem3928589 _45630 _45631 _45632 _45633 h1) (fun h2 : False => @lem3928591 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928593 (_45630 : int) (_45631 : int) (_45632 : int) (_45633 : int) (h1 : term197 _45630 _45631 _45632 _45633) : False.
Proof. exact (EQ_MP (@lem3928592 _45630 _45631 _45632 _45633 h1) (@lem3928591 _45630 _45631 _45632 _45633 h1)). Qed.
Lemma lem3928594 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) (h1 : term123 _45633 _45632 _45630 _45631) : term123 _45633 _45632 _45630 _45631.
Proof. exact (h1). Qed.
Lemma lem3928595 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) (h1 : term123 _45633 _45632 _45630 _45631) : term197 _45630 _45631 _45632 _45633.
Proof. exact (EQ_MP (@lem3927728 _45630 _45631 _45632 _45633) (@lem3928594 _45633 _45632 _45630 _45631 h1)). Qed.
Lemma lem3928596 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) (h1 : term123 _45633 _45632 _45630 _45631) : (term197 _45630 _45631 _45632 _45633) = False.
Proof. exact (prop_ext (fun h2 : term197 _45630 _45631 _45632 _45633 => @lem3928593 _45630 _45631 _45632 _45633 h2) (fun h2 : False => @lem3928595 _45633 _45632 _45630 _45631 h1)). Qed.
Lemma lem3928597 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) (h1 : term123 _45633 _45632 _45630 _45631) : False.
Proof. exact (EQ_MP (@lem3928596 _45633 _45632 _45630 _45631 h1) (@lem3928595 _45633 _45632 _45630 _45631 h1)). Qed.
Lemma lem3928598 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : term290 _45633 _45632 _45630 _45631.
Proof. exact (fun h0 : term123 _45633 _45632 _45630 _45631 => @lem3928597 _45633 _45632 _45630 _45631 h0). Qed.
Lemma lem3928599 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : term291 _45633 _45632 _45630 _45631.
Proof. exact (@lem1386578 (term292 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3928602 (_45633 : int) (_45632 : int) (_45630 : int) (_45631 : int) : term292 _45633 _45632 _45630 _45631.
Proof. exact (@lem3928599 _45633 _45632 _45630 _45631 (@lem3928598 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3928603 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term121 _45633 _45632 _45630 _45631) = (term85 _45630 _45631 _45633 _45632).
Proof. exact (SYM (@lem3927272 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3928604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3928605 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : (term292 _45633 _45632 _45630 _45631) = (term52 _45630 _45631 _45633 _45632).
Proof. exact (MK_COMB (@lem3928604) (@lem3928603 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3928606 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : term52 _45630 _45631 _45633 _45632.
Proof. exact (EQ_MP (@lem3928605 _45630 _45631 _45633 _45632) (@lem3928602 _45633 _45632 _45630 _45631)). Qed.
Lemma lem3928607 (_45630 : int) (_45631 : int) (_45633 : int) (_45632 : int) : term53 _45630 _45631 _45633 _45632.
Proof. exact (EQ_MP (@lem3927077 _45630 _45631 _45633 _45632) (@lem3928606 _45630 _45631 _45633 _45632)). Qed.
Lemma lem3928608 (a : nat) (b : nat) (x : nat) (n : nat) : term293 a b x n.
Proof. exact (@lem3928607 (int_of_num a) (int_of_num b) (term294 n x) (int_of_num n)). Qed.
Lemma lem3928609 (a : nat) (b : nat) (x : nat) (n : nat) : term295 a b x n.
Proof. exact (@lem3928608 a b x n (@lem3927067 a)). Qed.
Lemma lem3928610 (a : nat) (b : nat) (x : nat) (n : nat) : term296 a b x n.
Proof. exact (@lem3928609 a b x n (@lem3927070 b)). Qed.
Lemma lem3928611 (a : nat) (b : nat) (x : nat) (n : nat) : term297 a b x n.
Proof. exact (@lem3928610 a b x n (@lem3927073 n)). Qed.
Lemma lem3928612 (a : nat) (b : nat) (x : nat) (n : nat) : term47 a b x n.
Proof. exact (@lem3928611 a b x n (@lem3927076 n x)). Qed.
Lemma lem3928613 (a : nat) (b : nat) (x : nat) (n : nat) : (term47 a b x n) = (term8 a b x n).
Proof. exact (SYM (@lem3927064 a b x n)). Qed.
Lemma lem3928614 (a : nat) (b : nat) (x : nat) (n : nat) : term8 a b x n.
Proof. exact (EQ_MP (@lem3928613 a b x n) (@lem3928612 a b x n)). Qed.
Lemma lem3928615 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term8 a b x n) : term8 a b x n.
Proof. exact (h1). Qed.
Lemma lem3928616 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term9 a b x n) : term9 a b x n.
Proof. exact (h1). Qed.
Lemma lem3928617 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term9 a b x n) (h2 : term8 a b x n) : term3 a b x n.
Proof. exact (@lem3928615 a b x n h2 (@lem3928616 a b x n h1)). Qed.
Lemma lem3928618 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term9 a b x n) : term298 a b x n.
Proof. exact (fun h0 : term8 a b x n => @lem3928617 a b x n h1 h0). Qed.
Lemma lem3928619 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term8 a b x n) : term8 a b x n.
Proof. exact (h1). Qed.
Lemma lem3928620 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term9 a b x n) (h2 : term8 a b x n) : term3 a b x n.
Proof. exact (@lem3928618 a b x n h1 (@lem3928619 a b x n h2)). Qed.
Lemma lem3928621 (a : nat) (b : nat) (x : nat) (n : nat) (h1 : term8 a b x n) : term8 a b x n.
Proof. exact (fun h0 : term9 a b x n => @lem3928620 a b x n h0 h1). Qed.
Lemma lem3928622 (a : nat) (b : nat) (x : nat) (n : nat) : term299 a b x n.
Proof. exact (fun h0 : term8 a b x n => @lem3928621 a b x n h0). Qed.
Lemma lem3928637 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term300 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3928638 {_101153 : Type'} (s : _101153 -> Prop) (t : _101153 -> Prop) : (s = t) = (term300 _101153 s t).
Proof. exact (@lem3928637 _101153 s t). Qed.
Lemma lem3928639 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term301 _101149 _101153 s t) = (@IMAGE _101149 _101153 t s)) = (term302 _101149 _101153 t s).
Proof. exact (@lem3928638 _101153 (term301 _101149 _101153 s t) (@IMAGE _101149 _101153 t s)). Qed.
Lemma lem3928652 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term302 _101149 _101153 t s) = ((term301 _101149 _101153 s t) = (@IMAGE _101149 _101153 t s)).
Proof. exact (SYM (@lem3928639 _101149 _101153 t s)). Qed.
Lemma lem3928662 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term303 _83064 x P) = (term304 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem3928663 {_101153 : Type'} (P : type919 _101153) (x : _101153) : (term303 _101153 x P) = (term304 _101153 P x).
Proof. exact (@lem3928662 _101153 P x). Qed.
Lemma lem3928664 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) (x : _101153) : (term305 _101149 _101153 x s t) = (term306 _101149 _101153 s t x).
Proof. exact (@lem3928663 _101153 (term307 _101149 _101153 s t) x). Qed.
Lemma lem3928665 {_101149 _101153 : Type'} (GEN_PVAR_108 : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : (term308 _101149 _101153 s t GEN_PVAR_108) = (term309 _101149 _101153 GEN_PVAR_108 s t).
Proof. exact (eq_refl (term308 _101149 _101153 s t GEN_PVAR_108)). Qed.
Lemma lem3928666 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) : (term310 _101149 _101153 s t) = (term311 _101149 _101153 s t).
Proof. exact (fun_ext (fun GEN_PVAR_108 : _101153 => @lem3928665 _101149 _101153 GEN_PVAR_108 s t)). Qed.
Lemma lem3928667 {_101153 : Type'} : (@GSPEC _101153) = (@GSPEC _101153).
Proof. exact (eq_refl (@GSPEC _101153)). Qed.
Lemma lem3928668 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) : (term312 _101149 _101153 s t) = (term301 _101149 _101153 s t).
Proof. exact (MK_COMB (@lem3928667 _101153) (@lem3928666 _101149 _101153 s t)). Qed.
Lemma lem3928669 {_101153 : Type'} (x : _101153) : (@IN _101153 x) = (@IN _101153 x).
Proof. exact (eq_refl (@IN _101153 x)). Qed.
Lemma lem3928670 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : (term305 _101149 _101153 x s t) = (term313 _101149 _101153 x s t).
Proof. exact (MK_COMB (@lem3928669 _101153 x) (@lem3928668 _101149 _101153 s t)). Qed.
Lemma lem3928671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3928672 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : (term314 _101149 _101153 x s t) = (term315 _101149 _101153 x s t).
Proof. exact (MK_COMB (@lem3928671) (@lem3928670 _101149 _101153 x s t)). Qed.
Lemma lem3928673 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : (term306 _101149 _101153 s t x) = (term316 _101149 _101153 x s t).
Proof. exact (eq_refl (term306 _101149 _101153 s t x)). Qed.
Lemma lem3928674 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : ((term305 _101149 _101153 x s t) = (term306 _101149 _101153 s t x)) = ((term313 _101149 _101153 x s t) = (term316 _101149 _101153 x s t)).
Proof. exact (MK_COMB (@lem3928672 _101149 _101153 x s t) (@lem3928673 _101149 _101153 x s t)). Qed.
Lemma lem3928675 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (t : _101149 -> _101153) : (term313 _101149 _101153 x s t) = (term316 _101149 _101153 x s t).
Proof. exact (EQ_MP (@lem3928674 _101149 _101153 x s t) (@lem3928664 _101149 _101153 s t x)). Qed.
Lemma lem3928681 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3928682 {_101153 : Type'} (f : type1538 _101153) (y : Prop) : (term318 _101153 f y) = (f y).
Proof. exact (@lem3928681 Prop (_101153 -> Prop) f y). Qed.
Lemma lem3928683 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (s : _101149 -> Prop) : (term319 _101149 _101153 x x' s) = (term320 _101149 _101153 x x' s).
Proof. exact (@lem3928682 _101153 (term321 _101153 x) (@IN _101149 x' s)). Qed.
Lemma lem3928684 {_101153 : Type'} (p : Prop) (x : _101153) : (term322 _101153 x p) = (term323 _101153 p x).
Proof. exact (eq_refl (term322 _101153 x p)). Qed.
Lemma lem3928685 {_101153 : Type'} (x : _101153) : (term324 _101153 x) = (term321 _101153 x).
Proof. exact (fun_ext (fun p : Prop => @lem3928684 _101153 p x)). Qed.
Lemma lem3928686 {_101149 : Type'} (x : _101149) (s : _101149 -> Prop) : (@IN _101149 x s) = (@IN _101149 x s).
Proof. exact (eq_refl (@IN _101149 x s)). Qed.
Lemma lem3928687 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (s : _101149 -> Prop) : (term319 _101149 _101153 x x' s) = (term320 _101149 _101153 x x' s).
Proof. exact (MK_COMB (@lem3928685 _101153 x) (@lem3928686 _101149 x' s)). Qed.
Lemma lem3928688 {_101153 : Type'} : (@eq (_101153 -> Prop)) = (@eq (_101153 -> Prop)).
Proof. exact (eq_refl (@eq (_101153 -> Prop))). Qed.
Lemma lem3928689 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (s : _101149 -> Prop) : (term325 _101149 _101153 x x' s) = (term326 _101149 _101153 x x' s).
Proof. exact (MK_COMB (@lem3928688 _101153) (@lem3928687 _101149 _101153 x x' s)). Qed.
Lemma lem3928690 {_101149 _101153 : Type'} (x : _101149) (s : _101149 -> Prop) (x' : _101153) : (term320 _101149 _101153 x' x s) = (term327 _101149 _101153 x s x').
Proof. exact (eq_refl (term320 _101149 _101153 x' x s)). Qed.
Lemma lem3928691 {_101149 _101153 : Type'} (x : _101149) (s : _101149 -> Prop) (x' : _101153) : ((term319 _101149 _101153 x' x s) = (term320 _101149 _101153 x' x s)) = ((term320 _101149 _101153 x' x s) = (term327 _101149 _101153 x s x')).
Proof. exact (MK_COMB (@lem3928689 _101149 _101153 x' x s) (@lem3928690 _101149 _101153 x s x')). Qed.
Lemma lem3928692 {_101149 _101153 : Type'} (x : _101149) (s : _101149 -> Prop) (x' : _101153) : (term320 _101149 _101153 x' x s) = (term327 _101149 _101153 x s x').
Proof. exact (EQ_MP (@lem3928691 _101149 _101153 x s x') (@lem3928683 _101149 _101153 x' x s)). Qed.
Lemma lem3928696 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3928697 {_101149 : Type'} (P : _101149 -> Prop) (x : _101149) : (@IN _101149 x P) = (P x).
Proof. exact (@lem3928696 _101149 P x). Qed.
Lemma lem3928698 {_101149 : Type'} (s : _101149 -> Prop) (x : _101149) : (@IN _101149 x s) = (s x).
Proof. exact (@lem3928697 _101149 s x). Qed.
Lemma lem3928699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3928700 {_101149 : Type'} (s : _101149 -> Prop) (x : _101149) : (term328 _101149 x s) = (term329 _101149 s x).
Proof. exact (MK_COMB (@lem3928699) (@lem3928698 _101149 s x)). Qed.
Lemma lem3928703 {_101153 : Type'} (x : _101153) (t : _101153) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem3928704 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101149) (x' : _101153) (t : _101153) : (term330 _101149 _101153 x s x' t) = (term331 _101149 _101153 s x x' t).
Proof. exact (MK_COMB (@lem3928700 _101149 s x) (@lem3928703 _101153 x' t)). Qed.
Lemma lem3928707 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101149) (x' : _101153) : (term327 _101149 _101153 x s x') = (term332 _101149 _101153 s x x').
Proof. exact (fun_ext (fun t : _101153 => @lem3928704 _101149 _101153 s x x' t)). Qed.
Lemma lem3928708 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101149) (x' : _101153) : (term320 _101149 _101153 x' x s) = (term332 _101149 _101153 s x x').
Proof. exact (TRANS (@lem3928692 _101149 _101153 x s x') (@lem3928707 _101149 _101153 s x x')). Qed.
Lemma lem3928709 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x : _101149) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3928710 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term333 _101149 _101153 x s t x') = (term334 _101149 _101153 s x t x').
Proof. exact (MK_COMB (@lem3928708 _101149 _101153 s x' x) (@lem3928709 _101149 _101153 t x')). Qed.
Lemma lem3928712 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3928713 {_101153 : Type'} (f : _101153 -> Prop) (y : _101153) : (term335 _101153 f y) = (f y).
Proof. exact (@lem3928712 _101153 Prop f y). Qed.
Lemma lem3928714 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term336 _101149 _101153 s x t x') = (term334 _101149 _101153 s x t x').
Proof. exact (@lem3928713 _101153 (term332 _101149 _101153 s x' x) (t x')). Qed.
Lemma lem3928715 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101149) (x' : _101153) (t : _101153) : (term337 _101149 _101153 s x x' t) = (term331 _101149 _101153 s x x' t).
Proof. exact (eq_refl (term337 _101149 _101153 s x x' t)). Qed.
Lemma lem3928716 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101149) (x' : _101153) : (term338 _101149 _101153 s x x') = (term332 _101149 _101153 s x x').
Proof. exact (fun_ext (fun t : _101153 => @lem3928715 _101149 _101153 s x x' t)). Qed.
Lemma lem3928717 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x : _101149) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3928718 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term336 _101149 _101153 s x t x') = (term334 _101149 _101153 s x t x').
Proof. exact (MK_COMB (@lem3928716 _101149 _101153 s x' x) (@lem3928717 _101149 _101153 t x')). Qed.
Lemma lem3928719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3928720 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term339 _101149 _101153 s x t x') = (term340 _101149 _101153 s x t x').
Proof. exact (MK_COMB (@lem3928719) (@lem3928718 _101149 _101153 s x t x')). Qed.
Lemma lem3928721 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term334 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term334 _101149 _101153 s x t x')). Qed.
Lemma lem3928722 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : ((term336 _101149 _101153 s x t x') = (term334 _101149 _101153 s x t x')) = ((term334 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x')).
Proof. exact (MK_COMB (@lem3928720 _101149 _101153 s x t x') (@lem3928721 _101149 _101153 s x t x')). Qed.
Lemma lem3928723 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term334 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (EQ_MP (@lem3928722 _101149 _101153 s x t x') (@lem3928714 _101149 _101153 s x t x')). Qed.
Lemma lem3928728 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term333 _101149 _101153 x s t x') = (term341 _101149 _101153 s x t x').
Proof. exact (TRANS (@lem3928710 _101149 _101153 s x t x') (@lem3928723 _101149 _101153 s x t x')). Qed.
Lemma lem3928729 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term342 _101149 _101153 x s t) = (term343 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928728 _101149 _101153 s x t x')). Qed.
Lemma lem3928730 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3928731 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term316 _101149 _101153 x s t) = (term344 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928730 _101149) (@lem3928729 _101149 _101153 s x t)). Qed.
Lemma lem3928736 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term313 _101149 _101153 x s t) = (term344 _101149 _101153 s x t).
Proof. exact (TRANS (@lem3928675 _101149 _101153 x s t) (@lem3928731 _101149 _101153 s x t)). Qed.
Lemma lem3928737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3928738 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term315 _101149 _101153 x s t) = (term345 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928737) (@lem3928736 _101149 _101153 s x t)). Qed.
Lemma lem3928740 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term346 A B y f s) = (term347 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3928741 {_101149 _101153 : Type'} (y : _101153) (f : _101149 -> _101153) (s : _101149 -> Prop) : (term346 _101149 _101153 y f s) = (term347 _101149 _101153 y f s).
Proof. exact (@lem3928740 _101149 _101153 y f s). Qed.
Lemma lem3928742 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term346 _101149 _101153 x t s) = (term347 _101149 _101153 x t s).
Proof. exact (@lem3928741 _101149 _101153 x t s). Qed.
Lemma lem3928752 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3928753 {_101149 : Type'} (P : _101149 -> Prop) (x : _101149) : (@IN _101149 x P) = (P x).
Proof. exact (@lem3928752 _101149 P x). Qed.
Lemma lem3928754 {_101149 : Type'} (s : _101149 -> Prop) (x : _101149) : (@IN _101149 x s) = (s x).
Proof. exact (@lem3928753 _101149 s x). Qed.
Lemma lem3928755 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term348 _101149 _101153 x t x') = (term348 _101149 _101153 x t x').
Proof. exact (eq_refl (term348 _101149 _101153 x t x')). Qed.
Lemma lem3928756 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term349 _101149 _101153 x t x' s) = (term350 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3928755 _101149 _101153 x t x') (@lem3928754 _101149 s x')). Qed.
Lemma lem3928759 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term351 _101149 _101153 x t s) = (term352 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928756 _101149 _101153 x t s x')). Qed.
Lemma lem3928760 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3928761 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term347 _101149 _101153 x t s) = (term353 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3928760 _101149) (@lem3928759 _101149 _101153 x t s)). Qed.
Lemma lem3928766 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term346 _101149 _101153 x t s) = (term353 _101149 _101153 x t s).
Proof. exact (TRANS (@lem3928742 _101149 _101153 x t s) (@lem3928761 _101149 _101153 x t s)). Qed.
Lemma lem3928767 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term313 _101149 _101153 x s t) = (term346 _101149 _101153 x t s)) = ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s)).
Proof. exact (MK_COMB (@lem3928738 _101149 _101153 s x t) (@lem3928766 _101149 _101153 x t s)). Qed.
Lemma lem3928770 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term354 _101149 _101153 t s) = (term355 _101149 _101153 t s).
Proof. exact (fun_ext (fun x : _101153 => @lem3928767 _101149 _101153 x t s)). Qed.
Lemma lem3928771 {_101153 : Type'} : (@all _101153) = (@all _101153).
Proof. exact (eq_refl (@all _101153)). Qed.
Lemma lem3928772 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term302 _101149 _101153 t s) = (term356 _101149 _101153 t s).
Proof. exact (MK_COMB (@lem3928771 _101153) (@lem3928770 _101149 _101153 t s)). Qed.
Lemma lem3928777 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term356 _101149 _101153 t s) = (term302 _101149 _101153 t s).
Proof. exact (SYM (@lem3928772 _101149 _101153 t s)). Qed.
Lemma lem3928779 (p : Prop) : p = (term357 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3928780 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term356 _101149 _101153 t s) = (term358 _101149 _101153 t s).
Proof. exact (@lem3928779 (term356 _101149 _101153 t s)). Qed.
Lemma lem3928781 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term358 _101149 _101153 t s) = (term356 _101149 _101153 t s).
Proof. exact (SYM (@lem3928780 _101149 _101153 t s)). Qed.
Lemma lem3928782 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term359 _101149 _101153 t s) : term359 _101149 _101153 t s.
Proof. exact (h1). Qed.
Lemma lem3928785 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term358 _101149 _101153 t s) : term358 _101149 _101153 t s.
Proof. exact (h1). Qed.
Lemma lem3928786 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term360 _101149 _101153 t s.
Proof. exact (fun h0 : term358 _101149 _101153 t s => @lem3928785 _101149 _101153 t s h0). Qed.
Lemma lem3928787 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term360 _101149 _101153 t s) : term360 _101149 _101153 t s.
Proof. exact (h1). Qed.
Lemma lem3928788 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term358 _101149 _101153 t s) : term358 _101149 _101153 t s.
Proof. exact (h1). Qed.
Lemma lem3928789 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term358 _101149 _101153 t s) (h2 : term360 _101149 _101153 t s) : term358 _101149 _101153 t s.
Proof. exact (@lem3928787 _101149 _101153 t s h2 (@lem3928788 _101149 _101153 t s h1)). Qed.
Lemma lem3928790 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term358 _101149 _101153 t s) : term361 _101149 _101153 t s.
Proof. exact (fun h0 : term360 _101149 _101153 t s => @lem3928789 _101149 _101153 t s h1 h0). Qed.
Lemma lem3928791 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term360 _101149 _101153 t s) : term360 _101149 _101153 t s.
Proof. exact (h1). Qed.
Lemma lem3928792 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term358 _101149 _101153 t s) (h2 : term360 _101149 _101153 t s) : term358 _101149 _101153 t s.
Proof. exact (@lem3928790 _101149 _101153 t s h1 (@lem3928791 _101149 _101153 t s h2)). Qed.
Lemma lem3928793 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term360 _101149 _101153 t s) : term360 _101149 _101153 t s.
Proof. exact (fun h0 : term358 _101149 _101153 t s => @lem3928792 _101149 _101153 t s h0 h1). Qed.
Lemma lem3928794 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term362 _101149 _101153 t s.
Proof. exact (fun h0 : term360 _101149 _101153 t s => @lem3928793 _101149 _101153 t s h0). Qed.
Lemma lem3928797 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term360 _101149 _101153 t s.
Proof. exact (@lem3928794 _101149 _101153 t s (@lem3928786 _101149 _101153 t s)). Qed.
Lemma lem3928798 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term360 _101149 _101153 t s.
Proof. exact (@lem3928797 _101149 _101153 t s). Qed.
Lemma lem3928808 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3928809 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term358 _101149 _101153 t s) = (term363 _101149 _101153 t s).
Proof. exact (@lem3928808 (term359 _101149 _101153 t s)). Qed.
Lemma lem3928811 (t : Prop) : (term122 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3928812 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term363 _101149 _101153 t s) = (term356 _101149 _101153 t s).
Proof. exact (@lem3928811 (term356 _101149 _101153 t s)). Qed.
Lemma lem3928817 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term358 _101149 _101153 t s) = (term356 _101149 _101153 t s).
Proof. exact (TRANS (@lem3928809 _101149 _101153 t s) (@lem3928812 _101149 _101153 t s)). Qed.
Lemma lem3928882 {_101149 _101153 : Type'} (s : _101149 -> Prop) : (term364 _101149 _101153 s) = (term365 _101149 _101153 s).
Proof. exact (fun_ext (fun t : _101149 -> _101153 => @lem3928817 _101149 _101153 t s)). Qed.
Lemma lem3928883 {_101149 _101153 : Type'} : (@all (_101149 -> _101153)) = (@all (_101149 -> _101153)).
Proof. exact (eq_refl (@all (_101149 -> _101153))). Qed.
Lemma lem3928884 {_101149 _101153 : Type'} (s : _101149 -> Prop) : (term366 _101149 _101153 s) = (term367 _101149 _101153 s).
Proof. exact (MK_COMB (@lem3928883 _101149 _101153) (@lem3928882 _101149 _101153 s)). Qed.
Lemma lem3928889 {_101149 _101153 : Type'} : (term368 _101149 _101153) = (term369 _101149 _101153).
Proof. exact (fun_ext (fun s : _101149 -> Prop => @lem3928884 _101149 _101153 s)). Qed.
Lemma lem3928890 {_101149 : Type'} : (@all (_101149 -> Prop)) = (@all (_101149 -> Prop)).
Proof. exact (eq_refl (@all (_101149 -> Prop))). Qed.
Lemma lem3928899 {_101149 _101153 : Type'} : (term370 _101149 _101153) = (term371 _101149 _101153).
Proof. exact (MK_COMB (@lem3928890 _101149) (@lem3928889 _101149 _101153)). Qed.
Lemma lem3928904 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term350 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term350 _101149 _101153 x t s x')). Qed.
Lemma lem3928905 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term352 _101149 _101153 x t s) = (term352 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928904 _101149 _101153 x t s x')). Qed.
Lemma lem3928906 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3928907 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term353 _101149 _101153 x t s) = (term353 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3928906 _101149) (@lem3928905 _101149 _101153 x t s)). Qed.
Lemma lem3928912 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term341 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term341 _101149 _101153 s x t x')). Qed.
Lemma lem3928913 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term343 _101149 _101153 s x t) = (term343 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928912 _101149 _101153 s x t x')). Qed.
Lemma lem3928914 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3928915 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term344 _101149 _101153 s x t) = (term344 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928914 _101149) (@lem3928913 _101149 _101153 s x t)). Qed.
Lemma lem3928916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3928917 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term345 _101149 _101153 s x t) = (term345 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928916) (@lem3928915 _101149 _101153 s x t)). Qed.
Lemma lem3928918 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s)) = ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s)).
Proof. exact (MK_COMB (@lem3928917 _101149 _101153 s x t) (@lem3928907 _101149 _101153 x t s)). Qed.
Lemma lem3928919 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term355 _101149 _101153 t s) = (term355 _101149 _101153 t s).
Proof. exact (fun_ext (fun x : _101153 => @lem3928918 _101149 _101153 x t s)). Qed.
Lemma lem3928920 {_101153 : Type'} : (@all _101153) = (@all _101153).
Proof. exact (eq_refl (@all _101153)). Qed.
Lemma lem3928921 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term356 _101149 _101153 t s) = (term356 _101149 _101153 t s).
Proof. exact (MK_COMB (@lem3928920 _101153) (@lem3928919 _101149 _101153 t s)). Qed.
Lemma lem3928922 {_101149 _101153 : Type'} (s : _101149 -> Prop) : (term365 _101149 _101153 s) = (term365 _101149 _101153 s).
Proof. exact (fun_ext (fun t : _101149 -> _101153 => @lem3928921 _101149 _101153 t s)). Qed.
Lemma lem3928923 {_101149 _101153 : Type'} : (@all (_101149 -> _101153)) = (@all (_101149 -> _101153)).
Proof. exact (eq_refl (@all (_101149 -> _101153))). Qed.
Lemma lem3928924 {_101149 _101153 : Type'} (s : _101149 -> Prop) : (term367 _101149 _101153 s) = (term367 _101149 _101153 s).
Proof. exact (MK_COMB (@lem3928923 _101149 _101153) (@lem3928922 _101149 _101153 s)). Qed.
Lemma lem3928925 {_101149 _101153 : Type'} : (term369 _101149 _101153) = (term369 _101149 _101153).
Proof. exact (fun_ext (fun s : _101149 -> Prop => @lem3928924 _101149 _101153 s)). Qed.
Lemma lem3928926 {_101149 : Type'} : (@all (_101149 -> Prop)) = (@all (_101149 -> Prop)).
Proof. exact (eq_refl (@all (_101149 -> Prop))). Qed.
Lemma lem3928927 {_101149 _101153 : Type'} : (term371 _101149 _101153) = (term371 _101149 _101153).
Proof. exact (MK_COMB (@lem3928926 _101149) (@lem3928925 _101149 _101153)). Qed.
Lemma lem3928964 {_101149 _101153 : Type'} : (term370 _101149 _101153) = (term371 _101149 _101153).
Proof. exact (TRANS (@lem3928899 _101149 _101153) (@lem3928927 _101149 _101153)). Qed.
Lemma lem3928965 {_101149 _101153 : Type'} : (term371 _101149 _101153) = (term370 _101149 _101153).
Proof. exact (SYM (@lem3928964 _101149 _101153)). Qed.
Lemma lem3928967 (p : Prop) : p = (term357 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3928968 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s)) = (term372 _101149 _101153 x t s).
Proof. exact (@lem3928967 ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s))). Qed.
Lemma lem3928969 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term372 _101149 _101153 x t s) = ((term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s)).
Proof. exact (SYM (@lem3928968 _101149 _101153 x t s)). Qed.
Lemma lem3928970 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term373 _101149 _101153 x t s) : term373 _101149 _101153 x t s.
Proof. exact (h1). Qed.
Lemma lem3928979 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term374 _101149 _101153 s x t x') = (term375 _101149 _101153 s x t x').
Proof. exact (@lem17045 (s x') (x = (t x'))). Qed.
Lemma lem3928982 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term341 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term341 _101149 _101153 s x t x')). Qed.
Lemma lem3928983 {_101149 : Type'} (P : _101149 -> Prop) : (term376 _101149 P) = (term377 _101149 P).
Proof. exact (@lem18394 _101149 P). Qed.
Lemma lem3928984 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term378 _101149 _101153 s x t) = (term379 _101149 _101153 s x t).
Proof. exact (@lem3928983 _101149 (term343 _101149 _101153 s x t)). Qed.
Lemma lem3928985 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term380 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term380 _101149 _101153 s x t x')). Qed.
Lemma lem3928986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3928987 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term381 _101149 _101153 s x t x') = (term374 _101149 _101153 s x t x').
Proof. exact (MK_COMB (@lem3928986) (@lem3928985 _101149 _101153 s x t x')). Qed.
Lemma lem3928988 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term381 _101149 _101153 s x t x') = (term375 _101149 _101153 s x t x').
Proof. exact (TRANS (@lem3928987 _101149 _101153 s x t x') (@lem3928979 _101149 _101153 s x t x')). Qed.
Lemma lem3928989 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term382 _101149 _101153 s x t) = (term383 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928988 _101149 _101153 s x t x')). Qed.
Lemma lem3928990 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3928991 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term379 _101149 _101153 s x t) = (term384 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928990 _101149) (@lem3928989 _101149 _101153 s x t)). Qed.
Lemma lem3928992 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term378 _101149 _101153 s x t) = (term384 _101149 _101153 s x t).
Proof. exact (TRANS (@lem3928984 _101149 _101153 s x t) (@lem3928991 _101149 _101153 s x t)). Qed.
Lemma lem3928993 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term343 _101149 _101153 s x t) = (term343 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3928982 _101149 _101153 s x t x')). Qed.
Lemma lem3928994 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3928995 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term344 _101149 _101153 s x t) = (term344 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3928994 _101149) (@lem3928993 _101149 _101153 s x t)). Qed.
Lemma lem3929004 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term385 _101149 _101153 x t s x') = (term386 _101149 _101153 x t s x').
Proof. exact (@lem17045 (x = (t x')) (s x')). Qed.
Lemma lem3929007 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term350 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term350 _101149 _101153 x t s x')). Qed.
Lemma lem3929008 {_101149 : Type'} (P : _101149 -> Prop) : (term376 _101149 P) = (term377 _101149 P).
Proof. exact (@lem18394 _101149 P). Qed.
Lemma lem3929009 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term387 _101149 _101153 x t s) = (term388 _101149 _101153 x t s).
Proof. exact (@lem3929008 _101149 (term352 _101149 _101153 x t s)). Qed.
Lemma lem3929010 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term389 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term389 _101149 _101153 x t s x')). Qed.
Lemma lem3929011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3929012 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term390 _101149 _101153 x t s x') = (term385 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3929011) (@lem3929010 _101149 _101153 x t s x')). Qed.
Lemma lem3929013 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term390 _101149 _101153 x t s x') = (term386 _101149 _101153 x t s x').
Proof. exact (TRANS (@lem3929012 _101149 _101153 x t s x') (@lem3929004 _101149 _101153 x t s x')). Qed.
Lemma lem3929014 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term391 _101149 _101153 x t s) = (term392 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929013 _101149 _101153 x t s x')). Qed.
Lemma lem3929015 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3929016 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term388 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929015 _101149) (@lem3929014 _101149 _101153 x t s)). Qed.
Lemma lem3929017 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term387 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (TRANS (@lem3929009 _101149 _101153 x t s) (@lem3929016 _101149 _101153 x t s)). Qed.
Lemma lem3929018 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term352 _101149 _101153 x t s) = (term352 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929007 _101149 _101153 x t s x')). Qed.
Lemma lem3929019 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929020 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term353 _101149 _101153 x t s) = (term353 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929019 _101149) (@lem3929018 _101149 _101153 x t s)). Qed.
Lemma lem3929021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929022 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term394 _101149 _101153 s x t) = (term395 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929021) (@lem3928992 _101149 _101153 s x t)). Qed.
Lemma lem3929023 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term396 _101149 _101153 x t s) = (term397 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929022 _101149 _101153 s x t) (@lem3929020 _101149 _101153 x t s)). Qed.
Lemma lem3929024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929025 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term398 _101149 _101153 s x t) = (term398 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929024) (@lem3928995 _101149 _101153 s x t)). Qed.
Lemma lem3929026 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term399 _101149 _101153 x t s) = (term400 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929025 _101149 _101153 s x t) (@lem3929017 _101149 _101153 x t s)). Qed.
Lemma lem3929027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929028 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term401 _101149 _101153 x t s) = (term402 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929027) (@lem3929026 _101149 _101153 x t s)). Qed.
Lemma lem3929029 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term403 _101149 _101153 x t s) = (term404 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929028 _101149 _101153 x t s) (@lem3929023 _101149 _101153 x t s)). Qed.
Lemma lem3929030 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term373 _101149 _101153 x t s) = (term403 _101149 _101153 x t s).
Proof. exact (@lem17646 (term344 _101149 _101153 s x t) (term353 _101149 _101153 x t s)). Qed.
Lemma lem3929031 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term373 _101149 _101153 x t s) = (term404 _101149 _101153 x t s).
Proof. exact (TRANS (@lem3929030 _101149 _101153 x t s) (@lem3929029 _101149 _101153 x t s)). Qed.
Lemma lem3929190 {A : Type'} (P : A -> Prop) (Q : Prop) : (term405 A P Q) = (term406 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3929191 {_101149 : Type'} (P : _101149 -> Prop) (Q : Prop) : (term405 _101149 P Q) = (term406 _101149 P Q).
Proof. exact (@lem3929190 _101149 P Q). Qed.
Lemma lem3929192 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term407 _101149 _101153 x t s) = (term408 _101149 _101153 x t s).
Proof. exact (@lem3929191 _101149 (term343 _101149 _101153 s x t) (term393 _101149 _101153 x t s)). Qed.
Lemma lem3929193 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term380 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term380 _101149 _101153 s x t x')). Qed.
Lemma lem3929194 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term409 _101149 _101153 s x t) = (term343 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929193 _101149 _101153 s x t x')). Qed.
Lemma lem3929195 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929196 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term410 _101149 _101153 s x t) = (term344 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929195 _101149) (@lem3929194 _101149 _101153 s x t)). Qed.
Lemma lem3929197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929198 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term411 _101149 _101153 s x t) = (term398 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929197) (@lem3929196 _101149 _101153 s x t)). Qed.
Lemma lem3929199 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term393 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (eq_refl (term393 _101149 _101153 x t s)). Qed.
Lemma lem3929200 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term407 _101149 _101153 x t s) = (term400 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929198 _101149 _101153 s x t) (@lem3929199 _101149 _101153 x t s)). Qed.
Lemma lem3929201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929202 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term412 _101149 _101153 x t s) = (term413 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929201) (@lem3929200 _101149 _101153 x t s)). Qed.
Lemma lem3929203 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term380 _101149 _101153 s x t x') = (term341 _101149 _101153 s x t x').
Proof. exact (eq_refl (term380 _101149 _101153 s x t x')). Qed.
Lemma lem3929204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929205 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term414 _101149 _101153 s x t x') = (term415 _101149 _101153 s x t x').
Proof. exact (MK_COMB (@lem3929204) (@lem3929203 _101149 _101153 s x t x')). Qed.
Lemma lem3929206 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term393 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (eq_refl (term393 _101149 _101153 x t s)). Qed.
Lemma lem3929207 {_101149 _101153 : Type'} (x : _101149) (x' : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term416 _101149 _101153 x x' t s) = (term417 _101149 _101153 x x' t s).
Proof. exact (MK_COMB (@lem3929205 _101149 _101153 s x' t x) (@lem3929206 _101149 _101153 x' t s)). Qed.
Lemma lem3929208 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term418 _101149 _101153 x t s) = (term419 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929207 _101149 _101153 x' x t s)). Qed.
Lemma lem3929209 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929210 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term408 _101149 _101153 x t s) = (term420 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929209 _101149) (@lem3929208 _101149 _101153 x t s)). Qed.
Lemma lem3929211 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term407 _101149 _101153 x t s) = (term408 _101149 _101153 x t s)) = ((term400 _101149 _101153 x t s) = (term420 _101149 _101153 x t s)).
Proof. exact (MK_COMB (@lem3929202 _101149 _101153 x t s) (@lem3929210 _101149 _101153 x t s)). Qed.
Lemma lem3929212 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term400 _101149 _101153 x t s) = (term420 _101149 _101153 x t s).
Proof. exact (EQ_MP (@lem3929211 _101149 _101153 x t s) (@lem3929192 _101149 _101153 x t s)). Qed.
Lemma lem3929213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929214 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term402 _101149 _101153 x t s) = (term421 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929213) (@lem3929212 _101149 _101153 x t s)). Qed.
Lemma lem3929216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term422 A P Q) = (term423 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3929217 {_101149 : Type'} (P : Prop) (Q : _101149 -> Prop) : (term422 _101149 P Q) = (term423 _101149 P Q).
Proof. exact (@lem3929216 _101149 P Q). Qed.
Lemma lem3929218 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term424 _101149 _101153 x t s) = (term425 _101149 _101153 x t s).
Proof. exact (@lem3929217 _101149 (term384 _101149 _101153 s x t) (term352 _101149 _101153 x t s)). Qed.
Lemma lem3929219 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term389 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term389 _101149 _101153 x t s x')). Qed.
Lemma lem3929220 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term426 _101149 _101153 x t s) = (term352 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929219 _101149 _101153 x t s x')). Qed.
Lemma lem3929221 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929222 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term427 _101149 _101153 x t s) = (term353 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929221 _101149) (@lem3929220 _101149 _101153 x t s)). Qed.
Lemma lem3929223 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term395 _101149 _101153 s x t) = (term395 _101149 _101153 s x t).
Proof. exact (eq_refl (term395 _101149 _101153 s x t)). Qed.
Lemma lem3929224 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term424 _101149 _101153 x t s) = (term397 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929223 _101149 _101153 s x t) (@lem3929222 _101149 _101153 x t s)). Qed.
Lemma lem3929225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929226 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term428 _101149 _101153 x t s) = (term429 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929225) (@lem3929224 _101149 _101153 x t s)). Qed.
Lemma lem3929227 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term389 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term389 _101149 _101153 x t s x')). Qed.
Lemma lem3929228 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term395 _101149 _101153 s x t) = (term395 _101149 _101153 s x t).
Proof. exact (eq_refl (term395 _101149 _101153 s x t)). Qed.
Lemma lem3929229 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term430 _101149 _101153 x t s x') = (term431 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3929228 _101149 _101153 s x t) (@lem3929227 _101149 _101153 x t s x')). Qed.
Lemma lem3929230 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term432 _101149 _101153 x t s) = (term433 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929229 _101149 _101153 x t s x')). Qed.
Lemma lem3929231 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929232 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term425 _101149 _101153 x t s) = (term434 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929231 _101149) (@lem3929230 _101149 _101153 x t s)). Qed.
Lemma lem3929233 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term424 _101149 _101153 x t s) = (term425 _101149 _101153 x t s)) = ((term397 _101149 _101153 x t s) = (term434 _101149 _101153 x t s)).
Proof. exact (MK_COMB (@lem3929226 _101149 _101153 x t s) (@lem3929232 _101149 _101153 x t s)). Qed.
Lemma lem3929234 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term397 _101149 _101153 x t s) = (term434 _101149 _101153 x t s).
Proof. exact (EQ_MP (@lem3929233 _101149 _101153 x t s) (@lem3929218 _101149 _101153 x t s)). Qed.
Lemma lem3929235 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term404 _101149 _101153 x t s) = (term435 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929214 _101149 _101153 x t s) (@lem3929234 _101149 _101153 x t s)). Qed.
Lemma lem3929237 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term436 A P Q) = (term437 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3929238 {_101149 : Type'} (P : _101149 -> Prop) (Q : _101149 -> Prop) : (term436 _101149 P Q) = (term437 _101149 P Q).
Proof. exact (@lem3929237 _101149 P Q). Qed.
Lemma lem3929239 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term438 _101149 _101153 x t s) = (term439 _101149 _101153 x t s).
Proof. exact (@lem3929238 _101149 (term419 _101149 _101153 x t s) (term433 _101149 _101153 x t s)). Qed.
Lemma lem3929240 {_101149 _101153 : Type'} (x : _101149) (x' : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term440 _101149 _101153 x' t s x) = (term417 _101149 _101153 x x' t s).
Proof. exact (eq_refl (term440 _101149 _101153 x' t s x)). Qed.
Lemma lem3929241 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term441 _101149 _101153 x t s) = (term419 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929240 _101149 _101153 x' x t s)). Qed.
Lemma lem3929242 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929243 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term442 _101149 _101153 x t s) = (term420 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929242 _101149) (@lem3929241 _101149 _101153 x t s)). Qed.
Lemma lem3929244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929245 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term443 _101149 _101153 x t s) = (term421 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929244) (@lem3929243 _101149 _101153 x t s)). Qed.
Lemma lem3929246 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term444 _101149 _101153 x t s x') = (term431 _101149 _101153 x t s x').
Proof. exact (eq_refl (term444 _101149 _101153 x t s x')). Qed.
Lemma lem3929247 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term445 _101149 _101153 x t s) = (term433 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929246 _101149 _101153 x t s x')). Qed.
Lemma lem3929248 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929249 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term446 _101149 _101153 x t s) = (term434 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929248 _101149) (@lem3929247 _101149 _101153 x t s)). Qed.
Lemma lem3929250 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term438 _101149 _101153 x t s) = (term435 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929245 _101149 _101153 x t s) (@lem3929249 _101149 _101153 x t s)). Qed.
Lemma lem3929251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929252 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term447 _101149 _101153 x t s) = (term448 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929251) (@lem3929250 _101149 _101153 x t s)). Qed.
Lemma lem3929253 {_101149 _101153 : Type'} (x : _101149) (x' : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term440 _101149 _101153 x' t s x) = (term417 _101149 _101153 x x' t s).
Proof. exact (eq_refl (term440 _101149 _101153 x' t s x)). Qed.
Lemma lem3929254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929255 {_101149 _101153 : Type'} (x : _101149) (x' : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term449 _101149 _101153 x' t s x) = (term450 _101149 _101153 x x' t s).
Proof. exact (MK_COMB (@lem3929254) (@lem3929253 _101149 _101153 x x' t s)). Qed.
Lemma lem3929256 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term444 _101149 _101153 x t s x') = (term431 _101149 _101153 x t s x').
Proof. exact (eq_refl (term444 _101149 _101153 x t s x')). Qed.
Lemma lem3929257 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term451 _101149 _101153 x t s x') = (term452 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3929255 _101149 _101153 x' x t s) (@lem3929256 _101149 _101153 x t s x')). Qed.
Lemma lem3929258 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term453 _101149 _101153 x t s) = (term454 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929257 _101149 _101153 x t s x')). Qed.
Lemma lem3929259 {_101149 : Type'} : (@ex _101149) = (@ex _101149).
Proof. exact (eq_refl (@ex _101149)). Qed.
Lemma lem3929260 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term439 _101149 _101153 x t s) = (term455 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929259 _101149) (@lem3929258 _101149 _101153 x t s)). Qed.
Lemma lem3929261 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : ((term438 _101149 _101153 x t s) = (term439 _101149 _101153 x t s)) = ((term435 _101149 _101153 x t s) = (term455 _101149 _101153 x t s)).
Proof. exact (MK_COMB (@lem3929252 _101149 _101153 x t s) (@lem3929260 _101149 _101153 x t s)). Qed.
Lemma lem3929262 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term435 _101149 _101153 x t s) = (term455 _101149 _101153 x t s).
Proof. exact (EQ_MP (@lem3929261 _101149 _101153 x t s) (@lem3929239 _101149 _101153 x t s)). Qed.
Lemma lem3929264 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term404 _101149 _101153 x t s) = (term455 _101149 _101153 x t s).
Proof. exact (TRANS (@lem3929235 _101149 _101153 x t s) (@lem3929262 _101149 _101153 x t s)). Qed.
Lemma lem3929265 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term373 _101149 _101153 x t s) = (term455 _101149 _101153 x t s).
Proof. exact (TRANS (@lem3929031 _101149 _101153 x t s) (@lem3929264 _101149 _101153 x t s)). Qed.
Lemma lem3929266 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term373 _101149 _101153 x t s) : term455 _101149 _101153 x t s.
Proof. exact (EQ_MP (@lem3929265 _101149 _101153 x t s) (@lem3928970 _101149 _101153 x t s h1)). Qed.
Lemma lem3929267 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term452 _101149 _101153 x t s x') : term452 _101149 _101153 x t s x'.
Proof. exact (h1). Qed.
Lemma lem3929280 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term350 _101149 _101153 x t s x') = (term350 _101149 _101153 x t s x').
Proof. exact (eq_refl (term350 _101149 _101153 x t s x')). Qed.
Lemma lem3929297 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term375 _101149 _101153 s x t x') = (term375 _101149 _101153 s x t x').
Proof. exact (eq_refl (term375 _101149 _101153 s x t x')). Qed.
Lemma lem3929298 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term383 _101149 _101153 s x t) = (term383 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929297 _101149 _101153 s x t x')). Qed.
Lemma lem3929299 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3929300 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term384 _101149 _101153 s x t) = (term384 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929299 _101149) (@lem3929298 _101149 _101153 s x t)). Qed.
Lemma lem3929301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929302 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term395 _101149 _101153 s x t) = (term395 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929301) (@lem3929300 _101149 _101153 s x t)). Qed.
Lemma lem3929303 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term431 _101149 _101153 x t s x') = (term431 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3929302 _101149 _101153 s x t) (@lem3929280 _101149 _101153 x t s x')). Qed.
Lemma lem3929320 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term386 _101149 _101153 x t s x') = (term386 _101149 _101153 x t s x').
Proof. exact (eq_refl (term386 _101149 _101153 x t s x')). Qed.
Lemma lem3929321 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term392 _101149 _101153 x t s) = (term392 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929320 _101149 _101153 x t s x')). Qed.
Lemma lem3929322 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3929323 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term393 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929322 _101149) (@lem3929321 _101149 _101153 x t s)). Qed.
Lemma lem3929338 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term415 _101149 _101153 s x t x') = (term415 _101149 _101153 s x t x').
Proof. exact (eq_refl (term415 _101149 _101153 s x t x')). Qed.
Lemma lem3929339 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term417 _101149 _101153 x' x t s) = (term417 _101149 _101153 x' x t s).
Proof. exact (MK_COMB (@lem3929338 _101149 _101153 s x t x') (@lem3929323 _101149 _101153 x t s)). Qed.
Lemma lem3929340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929341 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term450 _101149 _101153 x' x t s) = (term450 _101149 _101153 x' x t s).
Proof. exact (MK_COMB (@lem3929340) (@lem3929339 _101149 _101153 x' x t s)). Qed.
Lemma lem3929342 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term452 _101149 _101153 x t s x') = (term452 _101149 _101153 x t s x').
Proof. exact (MK_COMB (@lem3929341 _101149 _101153 x' x t s) (@lem3929303 _101149 _101153 x t s x')). Qed.
Lemma lem3929343 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term452 _101149 _101153 x t s x') : term452 _101149 _101153 x t s x'.
Proof. exact (EQ_MP (@lem3929342 _101149 _101153 x t s x') (@lem3929267 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929344 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term417 _101149 _101153 x' x t s.
Proof. exact (h1). Qed.
Lemma lem3929345 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term431 _101149 _101153 x t s x'.
Proof. exact (h1). Qed.
Lemma lem3929346 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term393 _101149 _101153 x t s.
Proof. exact (proj2 (@lem3929344 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929347 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term341 _101149 _101153 s x t x'.
Proof. exact (proj1 (@lem3929344 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929350 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term350 _101149 _101153 x t s x'.
Proof. exact (proj2 (@lem3929345 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929351 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term384 _101149 _101153 s x t.
Proof. exact (proj1 (@lem3929345 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929361 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) : (term386 _101149 _101153 x t s x') = (term386 _101149 _101153 x t s x').
Proof. exact (eq_refl (term386 _101149 _101153 x t s x')). Qed.
Lemma lem3929362 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term392 _101149 _101153 x t s) = (term392 _101149 _101153 x t s).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929361 _101149 _101153 x t s x')). Qed.
Lemma lem3929363 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3929365 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term393 _101149 _101153 x t s) = (term393 _101149 _101153 x t s).
Proof. exact (MK_COMB (@lem3929363 _101149) (@lem3929362 _101149 _101153 x t s)). Qed.
Lemma lem3929366 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term393 _101149 _101153 x t s.
Proof. exact (EQ_MP (@lem3929365 _101149 _101153 x t s) (@lem3929346 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929382 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (x' : _101149) : (term375 _101149 _101153 s x t x') = (term375 _101149 _101153 s x t x').
Proof. exact (eq_refl (term375 _101149 _101153 s x t x')). Qed.
Lemma lem3929383 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term383 _101149 _101153 s x t) = (term383 _101149 _101153 s x t).
Proof. exact (fun_ext (fun x' : _101149 => @lem3929382 _101149 _101153 s x t x')). Qed.
Lemma lem3929384 {_101149 : Type'} : (@all _101149) = (@all _101149).
Proof. exact (eq_refl (@all _101149)). Qed.
Lemma lem3929386 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) : (term384 _101149 _101153 s x t) = (term384 _101149 _101153 s x t).
Proof. exact (MK_COMB (@lem3929384 _101149) (@lem3929383 _101149 _101153 s x t)). Qed.
Lemma lem3929387 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term384 _101149 _101153 s x t.
Proof. exact (EQ_MP (@lem3929386 _101149 _101153 s x t) (@lem3929351 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929396 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term456 _101149 _101153 x t s _45640.
Proof. exact (@lem3929366 _101149 _101153 x' x t s h1 _45640). Qed.
Lemma lem3929397 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term456 _101149 _101153 x t s _45640) = (term386 _101149 _101153 x t s _45640).
Proof. exact (eq_refl (term456 _101149 _101153 x t s _45640)). Qed.
Lemma lem3929399 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term457 _101149 _101153 s x t _45641.
Proof. exact (@lem3929387 _101149 _101153 x t s x' h1 _45641). Qed.
Lemma lem3929400 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (_45641 : _101149) : (term457 _101149 _101153 s x t _45641) = (term375 _101149 _101153 s x t _45641).
Proof. exact (eq_refl (term457 _101149 _101153 s x t _45641)). Qed.
Lemma lem3929407 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term386 _101149 _101153 x t s _45640.
Proof. exact (EQ_MP (@lem3929397 _101149 _101153 x t s _45640) (@lem3929396 _101149 _101153 _45640 x' x t s h1)). Qed.
Lemma lem3929411 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : x = (t x').
Proof. exact (proj2 (@lem3929347 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929417 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term375 _101149 _101153 s x t _45641.
Proof. exact (EQ_MP (@lem3929400 _101149 _101153 s x t _45641) (@lem3929399 _101149 _101153 _45641 x t s x' h1)). Qed.
Lemma lem3929419 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : x = (t x').
Proof. exact (proj1 (@lem3929350 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929436 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term458 _101149 _101153 t s _45640) = (term458 _101149 _101153 t s _45640).
Proof. exact (eq_refl (term458 _101149 _101153 t s _45640)). Qed.
Lemma lem3929437 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : (term459 _101149 _101153 t s _45640 x) = (term460 _101149 _101153 s _45640 t x').
Proof. exact (MK_COMB (@lem3929436 _101149 _101153 t s _45640) (@lem3929411 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929438 {_101149 _101153 : Type'} (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term460 _101149 _101153 s _45640 t x') = (term461 _101149 _101153 x' t s _45640).
Proof. exact (eq_refl (term460 _101149 _101153 s _45640 t x')). Qed.
Lemma lem3929439 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) (x : _101153) : (term462 _101149 _101153 t s _45640 x) = (term462 _101149 _101153 t s _45640 x).
Proof. exact (eq_refl (term462 _101149 _101153 t s _45640 x)). Qed.
Lemma lem3929440 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : ((term459 _101149 _101153 t s _45640 x) = (term460 _101149 _101153 s _45640 t x')) = ((term459 _101149 _101153 t s _45640 x) = (term461 _101149 _101153 x' t s _45640)).
Proof. exact (MK_COMB (@lem3929439 _101149 _101153 t s _45640 x) (@lem3929438 _101149 _101153 x' t s _45640)). Qed.
Lemma lem3929441 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term459 _101149 _101153 t s _45640 x) = (term386 _101149 _101153 x t s _45640).
Proof. exact (eq_refl (term459 _101149 _101153 t s _45640 x)). Qed.
Lemma lem3929442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929443 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term462 _101149 _101153 t s _45640 x) = (term463 _101149 _101153 x t s _45640).
Proof. exact (MK_COMB (@lem3929442) (@lem3929441 _101149 _101153 x t s _45640)). Qed.
Lemma lem3929444 {_101149 _101153 : Type'} (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term461 _101149 _101153 x' t s _45640) = (term461 _101149 _101153 x' t s _45640).
Proof. exact (eq_refl (term461 _101149 _101153 x' t s _45640)). Qed.
Lemma lem3929445 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : ((term459 _101149 _101153 t s _45640 x) = (term461 _101149 _101153 x' t s _45640)) = ((term386 _101149 _101153 x t s _45640) = (term461 _101149 _101153 x' t s _45640)).
Proof. exact (MK_COMB (@lem3929443 _101149 _101153 x t s _45640) (@lem3929444 _101149 _101153 x' t s _45640)). Qed.
Lemma lem3929446 {_101149 _101153 : Type'} (x : _101153) (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : ((term459 _101149 _101153 t s _45640 x) = (term460 _101149 _101153 s _45640 t x')) = ((term386 _101149 _101153 x t s _45640) = (term461 _101149 _101153 x' t s _45640)).
Proof. exact (TRANS (@lem3929440 _101149 _101153 x x' t s _45640) (@lem3929445 _101149 _101153 x x' t s _45640)). Qed.
Lemma lem3929447 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : (term386 _101149 _101153 x t s _45640) = (term461 _101149 _101153 x' t s _45640).
Proof. exact (EQ_MP (@lem3929446 _101149 _101153 x x' t s _45640) (@lem3929437 _101149 _101153 _45640 x' x t s h1)). Qed.
Lemma lem3929448 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term461 _101149 _101153 x' t s _45640.
Proof. exact (EQ_MP (@lem3929447 _101149 _101153 _45640 x' x t s h1) (@lem3929407 _101149 _101153 _45640 x' x t s h1)). Qed.
Lemma lem3929477 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) (_45641 : _101149) : (term464 _101149 _101153 s t _45641) = (term464 _101149 _101153 s t _45641).
Proof. exact (eq_refl (term464 _101149 _101153 s t _45641)). Qed.
Lemma lem3929478 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : (term465 _101149 _101153 s t _45641 x) = (term466 _101149 _101153 s _45641 t x').
Proof. exact (MK_COMB (@lem3929477 _101149 _101153 s t _45641) (@lem3929419 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929479 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : (term466 _101149 _101153 s _45641 t x') = (term467 _101149 _101153 s x' t _45641).
Proof. exact (eq_refl (term466 _101149 _101153 s _45641 t x')). Qed.
Lemma lem3929480 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) (_45641 : _101149) (x : _101153) : (term468 _101149 _101153 s t _45641 x) = (term468 _101149 _101153 s t _45641 x).
Proof. exact (eq_refl (term468 _101149 _101153 s t _45641 x)). Qed.
Lemma lem3929481 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : ((term465 _101149 _101153 s t _45641 x) = (term466 _101149 _101153 s _45641 t x')) = ((term465 _101149 _101153 s t _45641 x) = (term467 _101149 _101153 s x' t _45641)).
Proof. exact (MK_COMB (@lem3929480 _101149 _101153 s t _45641 x) (@lem3929479 _101149 _101153 s x' t _45641)). Qed.
Lemma lem3929482 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (_45641 : _101149) : (term465 _101149 _101153 s t _45641 x) = (term375 _101149 _101153 s x t _45641).
Proof. exact (eq_refl (term465 _101149 _101153 s t _45641 x)). Qed.
Lemma lem3929483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929484 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x : _101153) (t : _101149 -> _101153) (_45641 : _101149) : (term468 _101149 _101153 s t _45641 x) = (term469 _101149 _101153 s x t _45641).
Proof. exact (MK_COMB (@lem3929483) (@lem3929482 _101149 _101153 s x t _45641)). Qed.
Lemma lem3929485 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : (term467 _101149 _101153 s x' t _45641) = (term467 _101149 _101153 s x' t _45641).
Proof. exact (eq_refl (term467 _101149 _101153 s x' t _45641)). Qed.
Lemma lem3929486 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : ((term465 _101149 _101153 s t _45641 x) = (term467 _101149 _101153 s x' t _45641)) = ((term375 _101149 _101153 s x t _45641) = (term467 _101149 _101153 s x' t _45641)).
Proof. exact (MK_COMB (@lem3929484 _101149 _101153 s x t _45641) (@lem3929485 _101149 _101153 s x' t _45641)). Qed.
Lemma lem3929487 {_101149 _101153 : Type'} (x : _101153) (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : ((term465 _101149 _101153 s t _45641 x) = (term466 _101149 _101153 s _45641 t x')) = ((term375 _101149 _101153 s x t _45641) = (term467 _101149 _101153 s x' t _45641)).
Proof. exact (TRANS (@lem3929481 _101149 _101153 x s x' t _45641) (@lem3929486 _101149 _101153 x s x' t _45641)). Qed.
Lemma lem3929488 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : (term375 _101149 _101153 s x t _45641) = (term467 _101149 _101153 s x' t _45641).
Proof. exact (EQ_MP (@lem3929487 _101149 _101153 x s x' t _45641) (@lem3929478 _101149 _101153 _45641 x t s x' h1)). Qed.
Lemma lem3929489 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term467 _101149 _101153 s x' t _45641.
Proof. exact (EQ_MP (@lem3929488 _101149 _101153 _45641 x t s x' h1) (@lem3929417 _101149 _101153 _45641 x t s x' h1)). Qed.
Lemma lem3929529 {_101153 : Type'} (x : _101153) : x = x.
Proof. exact (@lem21386 _101153 x). Qed.
Lemma lem3929530 {_101153 : Type'} (x : _101153) : x = x.
Proof. exact (@lem3929529 _101153 x). Qed.
Lemma lem3929531 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (t x') = (t x').
Proof. exact (@lem3929530 _101153 (t x')). Qed.
Lemma lem3929532 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : term470 _101149 _101153 t x'.
Proof. exact (fun h0 : term471 _101149 _101153 t x' => @lem3929531 _101149 _101153 t x'). Qed.
Lemma lem3929534 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929535 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (term470 _101149 _101153 t x') = ((t x') = (t x')).
Proof. exact (@lem3929534 ((t x') = (t x'))). Qed.
Lemma lem3929536 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (t x') = (t x').
Proof. exact (EQ_MP (@lem3929535 _101149 _101153 t x') (@lem3929532 _101149 _101153 t x')). Qed.
Lemma lem3929538 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : s x'.
Proof. exact (proj1 (@lem3929347 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929539 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term473 _101149 s x'.
Proof. exact (fun h0 : term474 _101149 s x' => @lem3929538 _101149 _101153 x' x t s h1). Qed.
Lemma lem3929541 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929542 {_101149 : Type'} (s : _101149 -> Prop) (x' : _101149) : (term473 _101149 s x') = (s x').
Proof. exact (@lem3929541 (s x')). Qed.
Lemma lem3929543 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : s x'.
Proof. exact (EQ_MP (@lem3929542 _101149 s x') (@lem3929539 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929545 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3929546 {_101149 _101153 : Type'} (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term461 _101149 _101153 x' t s _45640) = (term477 _101149 _101153 x' t s _45640).
Proof. exact (@lem3929545 ((t x') = (t _45640)) (s _45640)). Qed.
Lemma lem3929548 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3929549 {_101149 _101153 : Type'} (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term477 _101149 _101153 x' t s _45640) = (term478 _101149 _101153 x' t s _45640).
Proof. exact (@lem3929548 (term479 _101149 _101153 x' t s _45640)). Qed.
Lemma lem3929550 {_101149 _101153 : Type'} (x' : _101149) (t : _101149 -> _101153) (s : _101149 -> Prop) (_45640 : _101149) : (term461 _101149 _101153 x' t s _45640) = (term478 _101149 _101153 x' t s _45640).
Proof. exact (TRANS (@lem3929546 _101149 _101153 x' t s _45640) (@lem3929549 _101149 _101153 x' t s _45640)). Qed.
Lemma lem3929552 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term480 _101149 _101153 t s x'.
Proof. exact (conj (@lem3929536 _101149 _101153 t x') (@lem3929543 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929554 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term478 _101149 _101153 x' t s _45640.
Proof. exact (EQ_MP (@lem3929550 _101149 _101153 x' t s _45640) (@lem3929448 _101149 _101153 _45640 x' x t s h1)). Qed.
Lemma lem3929555 {_101149 _101153 : Type'} (_45640 : _101149) (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term478 _101149 _101153 x' t s _45640.
Proof. exact (@lem3929554 _101149 _101153 _45640 x' x t s h1). Qed.
Lemma lem3929556 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term481 _101149 _101153 t s x'.
Proof. exact (@lem3929555 _101149 _101153 x' x' x t s h1). Qed.
Lemma lem3929559 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : False.
Proof. exact (@lem3929556 _101149 _101153 x' x t s h1 (@lem3929552 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929560 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : term482.
Proof. exact (fun h0 : ~ False => @lem3929559 _101149 _101153 x' x t s h1). Qed.
Lemma lem3929562 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929563 : term482 = False.
Proof. exact (@lem3929562 False). Qed.
Lemma lem3929590 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : s x'.
Proof. exact (proj2 (@lem3929350 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929591 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term473 _101149 s x'.
Proof. exact (fun h0 : term474 _101149 s x' => @lem3929590 _101149 _101153 x t s x' h1). Qed.
Lemma lem3929593 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929594 {_101149 : Type'} (s : _101149 -> Prop) (x' : _101149) : (term473 _101149 s x') = (s x').
Proof. exact (@lem3929593 (s x')). Qed.
Lemma lem3929595 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : s x'.
Proof. exact (EQ_MP (@lem3929594 _101149 s x') (@lem3929591 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929597 {_101153 : Type'} (x : _101153) : x = x.
Proof. exact (@lem21386 _101153 x). Qed.
Lemma lem3929598 {_101153 : Type'} (x : _101153) : x = x.
Proof. exact (@lem3929597 _101153 x). Qed.
Lemma lem3929599 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (t x') = (t x').
Proof. exact (@lem3929598 _101153 (t x')). Qed.
Lemma lem3929600 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : term470 _101149 _101153 t x'.
Proof. exact (fun h0 : term471 _101149 _101153 t x' => @lem3929599 _101149 _101153 t x'). Qed.
Lemma lem3929602 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929603 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (term470 _101149 _101153 t x') = ((t x') = (t x')).
Proof. exact (@lem3929602 ((t x') = (t x'))). Qed.
Lemma lem3929604 {_101149 _101153 : Type'} (t : _101149 -> _101153) (x' : _101149) : (t x') = (t x').
Proof. exact (EQ_MP (@lem3929603 _101149 _101153 t x') (@lem3929600 _101149 _101153 t x')). Qed.
Lemma lem3929606 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3929607 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : (term467 _101149 _101153 s x' t _45641) = (term483 _101149 _101153 s x' t _45641).
Proof. exact (@lem3929606 (s _45641) ((t x') = (t _45641))). Qed.
Lemma lem3929609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3929610 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : (term483 _101149 _101153 s x' t _45641) = (term484 _101149 _101153 s x' t _45641).
Proof. exact (@lem3929609 (term485 _101149 _101153 s x' t _45641)). Qed.
Lemma lem3929611 {_101149 _101153 : Type'} (s : _101149 -> Prop) (x' : _101149) (t : _101149 -> _101153) (_45641 : _101149) : (term467 _101149 _101153 s x' t _45641) = (term484 _101149 _101153 s x' t _45641).
Proof. exact (TRANS (@lem3929607 _101149 _101153 s x' t _45641) (@lem3929610 _101149 _101153 s x' t _45641)). Qed.
Lemma lem3929613 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term486 _101149 _101153 s t x'.
Proof. exact (conj (@lem3929595 _101149 _101153 x t s x' h1) (@lem3929604 _101149 _101153 t x')). Qed.
Lemma lem3929615 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term484 _101149 _101153 s x' t _45641.
Proof. exact (EQ_MP (@lem3929611 _101149 _101153 s x' t _45641) (@lem3929489 _101149 _101153 _45641 x t s x' h1)). Qed.
Lemma lem3929616 {_101149 _101153 : Type'} (_45641 : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term484 _101149 _101153 s x' t _45641.
Proof. exact (@lem3929615 _101149 _101153 _45641 x t s x' h1). Qed.
Lemma lem3929617 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term487 _101149 _101153 s t x'.
Proof. exact (@lem3929616 _101149 _101153 x' x t s x' h1). Qed.
Lemma lem3929620 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : False.
Proof. exact (@lem3929617 _101149 _101153 x t s x' h1 (@lem3929613 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929621 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : term482.
Proof. exact (fun h0 : ~ False => @lem3929620 _101149 _101153 x t s x' h1). Qed.
Lemma lem3929623 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3929624 : term482 = False.
Proof. exact (@lem3929623 False). Qed.
Lemma lem3929626 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term431 _101149 _101153 x t s x') : False.
Proof. exact (EQ_MP (@lem3929624) (@lem3929621 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929627 {_101149 _101153 : Type'} (x' : _101149) (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term417 _101149 _101153 x' x t s) : False.
Proof. exact (EQ_MP (@lem3929563) (@lem3929560 _101149 _101153 x' x t s h1)). Qed.
Lemma lem3929628 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term452 _101149 _101153 x t s x') : False.
Proof. exact (or_elim (@lem3929343 _101149 _101153 x t s x' h1) (fun h0 : term417 _101149 _101153 x' x t s => @lem3929627 _101149 _101153 x' x t s h0) (fun h0 : term431 _101149 _101153 x t s x' => @lem3929626 _101149 _101153 x t s x' h0)). Qed.
Lemma lem3929629 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term452 _101149 _101153 x t s x') : (term452 _101149 _101153 x t s x') = False.
Proof. exact (prop_ext (fun h2 : term452 _101149 _101153 x t s x' => @lem3929628 _101149 _101153 x t s x' h1) (fun h2 : False => @lem3929343 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929630 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (x' : _101149) (h1 : term452 _101149 _101153 x t s x') : False.
Proof. exact (EQ_MP (@lem3929629 _101149 _101153 x t s x' h1) (@lem3929343 _101149 _101153 x t s x' h1)). Qed.
Lemma lem3929631 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term373 _101149 _101153 x t s) : False.
Proof. exact (ex_elim (@lem3929266 _101149 _101153 x t s h1) (fun x' : _101149 => fun h0 : term454 _101149 _101153 x t s x' => @lem3929630 _101149 _101153 x t s x' h0)). Qed.
Lemma lem3929632 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term373 _101149 _101153 x t s) : (term373 _101149 _101153 x t s) = False.
Proof. exact (prop_ext (fun h2 : term373 _101149 _101153 x t s => @lem3929631 _101149 _101153 x t s h1) (fun h2 : False => @lem3928970 _101149 _101153 x t s h1)). Qed.
Lemma lem3929633 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term373 _101149 _101153 x t s) : False.
Proof. exact (EQ_MP (@lem3929632 _101149 _101153 x t s h1) (@lem3928970 _101149 _101153 x t s h1)). Qed.
Lemma lem3929634 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : term372 _101149 _101153 x t s.
Proof. exact (fun h0 : term373 _101149 _101153 x t s => @lem3929633 _101149 _101153 x t s h0). Qed.
Lemma lem3929635 {_101149 _101153 : Type'} (x : _101153) (t : _101149 -> _101153) (s : _101149 -> Prop) : (term344 _101149 _101153 s x t) = (term353 _101149 _101153 x t s).
Proof. exact (EQ_MP (@lem3928969 _101149 _101153 x t s) (@lem3929634 _101149 _101153 x t s)). Qed.
Lemma lem3929640 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term356 _101149 _101153 t s.
Proof. exact (fun x : _101153 => @lem3929635 _101149 _101153 x t s). Qed.
Lemma lem3929645 {_101149 _101153 : Type'} (s : _101149 -> Prop) : term367 _101149 _101153 s.
Proof. exact (fun t : _101149 -> _101153 => @lem3929640 _101149 _101153 t s). Qed.
Lemma lem3929650 {_101149 _101153 : Type'} : term371 _101149 _101153.
Proof. exact (fun s : _101149 -> Prop => @lem3929645 _101149 _101153 s). Qed.
Lemma lem3929651 {_101149 _101153 : Type'} : term370 _101149 _101153.
Proof. exact (EQ_MP (@lem3928965 _101149 _101153) (@lem3929650 _101149 _101153)). Qed.
Lemma lem3929652 {_101149 _101153 : Type'} (s : _101149 -> Prop) : term488 _101149 _101153 s.
Proof. exact (@lem3929651 _101149 _101153 s). Qed.
Lemma lem3929653 {_101149 _101153 : Type'} (s : _101149 -> Prop) : (term488 _101149 _101153 s) = (term366 _101149 _101153 s).
Proof. exact (eq_refl (term488 _101149 _101153 s)). Qed.
Lemma lem3929654 {_101149 _101153 : Type'} (s : _101149 -> Prop) : term366 _101149 _101153 s.
Proof. exact (EQ_MP (@lem3929653 _101149 _101153 s) (@lem3929652 _101149 _101153 s)). Qed.
Lemma lem3929655 {_101149 _101153 : Type'} (s : _101149 -> Prop) (t : _101149 -> _101153) : term489 _101149 _101153 s t.
Proof. exact (@lem3929654 _101149 _101153 s t). Qed.
Lemma lem3929656 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term489 _101149 _101153 s t) = (term358 _101149 _101153 t s).
Proof. exact (eq_refl (term489 _101149 _101153 s t)). Qed.
Lemma lem3929657 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term358 _101149 _101153 t s.
Proof. exact (EQ_MP (@lem3929656 _101149 _101153 t s) (@lem3929655 _101149 _101153 s t)). Qed.
Lemma lem3929659 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term358 _101149 _101153 t s.
Proof. exact (@lem3928798 _101149 _101153 t s (@lem3929657 _101149 _101153 t s)). Qed.
Lemma lem3929660 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term359 _101149 _101153 t s) : False.
Proof. exact (@lem3929659 _101149 _101153 t s (@lem3928782 _101149 _101153 t s h1)). Qed.
Lemma lem3929661 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term359 _101149 _101153 t s) : (term359 _101149 _101153 t s) = False.
Proof. exact (prop_ext (fun h2 : term359 _101149 _101153 t s => @lem3929660 _101149 _101153 t s h1) (fun h2 : False => @lem3928782 _101149 _101153 t s h1)). Qed.
Lemma lem3929662 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) (h1 : term359 _101149 _101153 t s) : False.
Proof. exact (EQ_MP (@lem3929661 _101149 _101153 t s h1) (@lem3928782 _101149 _101153 t s h1)). Qed.
Lemma lem3929663 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term358 _101149 _101153 t s.
Proof. exact (fun h0 : term359 _101149 _101153 t s => @lem3929662 _101149 _101153 t s h0). Qed.
Lemma lem3929664 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term356 _101149 _101153 t s.
Proof. exact (EQ_MP (@lem3928781 _101149 _101153 t s) (@lem3929663 _101149 _101153 t s)). Qed.
Lemma lem3929665 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : term302 _101149 _101153 t s.
Proof. exact (EQ_MP (@lem3928777 _101149 _101153 t s) (@lem3929664 _101149 _101153 t s)). Qed.
Lemma lem3929667 {A : Type'} (h1 : term490 A) : term490 A.
Proof. exact (h1). Qed.
Lemma lem3929668 {A : Type'} (s : A -> Prop) (h1 : term490 A) : term491 A s.
Proof. exact (@lem3929667 A h1 s). Qed.
Lemma lem3929669 {A : Type'} (s : A -> Prop) : (term491 A s) = (term492 A s).
Proof. exact (eq_refl (term491 A s)). Qed.
Lemma lem3929670 {A : Type'} (s : A -> Prop) (h1 : term490 A) : term492 A s.
Proof. exact (EQ_MP (@lem3929669 A s) (@lem3929668 A s h1)). Qed.
Lemma lem3929671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term490 A) : term493 A s t.
Proof. exact (@lem3929670 A s h1 t). Qed.
Lemma lem3929672 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term493 A s t) = (term494 A s t).
Proof. exact (eq_refl (term493 A s t)). Qed.
Lemma lem3929673 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term490 A) : term494 A s t.
Proof. exact (EQ_MP (@lem3929672 A s t) (@lem3929671 A s t h1)). Qed.
Lemma lem3929674 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term495 A s t) : term495 A s t.
Proof. exact (h1). Qed.
Lemma lem3929675 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term490 A) (h2 : term495 A s t) : term496 A s t.
Proof. exact (@lem3929673 A s t h1 (@lem3929674 A s t h2)). Qed.
Lemma lem3929676 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term495 A s t) : term497 A s t.
Proof. exact (fun h0 : term490 A => @lem3929675 A s t h0 h1). Qed.
Lemma lem3929677 {A : Type'} (h1 : term490 A) : term490 A.
Proof. exact (h1). Qed.
Lemma lem3929678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term490 A) (h2 : term495 A s t) : term496 A s t.
Proof. exact (@lem3929676 A s t h2 (@lem3929677 A h1)). Qed.
Lemma lem3929679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term490 A) : term494 A s t.
Proof. exact (fun h0 : term495 A s t => @lem3929678 A s t h1 h0). Qed.
Lemma lem3929680 {A : Type'} (s : A -> Prop) (h1 : term490 A) : term492 A s.
Proof. exact (fun t : A -> Prop => @lem3929679 A s t h1). Qed.
Lemma lem3929681 {A : Type'} (h1 : term490 A) : term490 A.
Proof. exact (fun s : A -> Prop => @lem3929680 A s h1). Qed.
Lemma lem3929682 {A : Type'} : term498 A.
Proof. exact (fun h0 : term490 A => @lem3929681 A h0). Qed.
Lemma lem3929683 {A : Type'} : term490 A.
Proof. exact (@lem3929682 A (@lem3924614 A)). Qed.
Lemma lem3929684 {A : Type'} (s : A -> Prop) : term491 A s.
Proof. exact (@lem3929683 A s). Qed.
Lemma lem3929685 {A : Type'} (s : A -> Prop) : (term491 A s) = (term492 A s).
Proof. exact (eq_refl (term491 A s)). Qed.
Lemma lem3929686 {A : Type'} (s : A -> Prop) : term492 A s.
Proof. exact (EQ_MP (@lem3929685 A s) (@lem3929684 A s)). Qed.
Lemma lem3929687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term493 A s t.
Proof. exact (@lem3929686 A s t). Qed.
Lemma lem3929688 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term493 A s t) = (term494 A s t).
Proof. exact (eq_refl (term493 A s t)). Qed.
Lemma lem3929690 (h1 : term499) : term499.
Proof. exact (h1). Qed.
Lemma lem3929691 (m : nat) (h1 : term499) : term500 m.
Proof. exact (@lem3929690 h1 m). Qed.
Lemma lem3929692 (m : nat) : (term500 m) = (term501 m).
Proof. exact (eq_refl (term500 m)). Qed.
Lemma lem3929693 (m : nat) (h1 : term499) : term501 m.
Proof. exact (EQ_MP (@lem3929692 m) (@lem3929691 m h1)). Qed.
Lemma lem3929694 (m : nat) (n : nat) (h1 : term499) : term502 m n.
Proof. exact (@lem3929693 m h1 n). Qed.
Lemma lem3929695 (n : nat) (m : nat) : (term502 m n) = (term503 n m).
Proof. exact (eq_refl (term502 m n)). Qed.
Lemma lem3929696 (n : nat) (m : nat) (h1 : term499) : term503 n m.
Proof. exact (EQ_MP (@lem3929695 n m) (@lem3929694 m n h1)). Qed.
Lemma lem3929697 (n : nat) (m : nat) (p : nat) (h1 : term499) : term504 n m p.
Proof. exact (@lem3929696 n m h1 p). Qed.
Lemma lem3929698 (n : nat) (m : nat) (p : nat) : (term504 n m p) = (term505 n m p).
Proof. exact (eq_refl (term504 n m p)). Qed.
Lemma lem3929699 (n : nat) (m : nat) (p : nat) (h1 : term499) : term505 n m p.
Proof. exact (EQ_MP (@lem3929698 n m p) (@lem3929697 n m p h1)). Qed.
Lemma lem3929700 (m : nat) (n : nat) (p : nat) (h1 : term506 m n p) : term506 m n p.
Proof. exact (h1). Qed.
Lemma lem3929701 (m : nat) (n : nat) (p : nat) (h1 : term499) (h2 : term506 m n p) : Peano.le m p.
Proof. exact (@lem3929699 n m p h1 (@lem3929700 m n p h2)). Qed.
Lemma lem3929702 (m : nat) (n : nat) (p : nat) (h1 : term506 m n p) : term507 m p.
Proof. exact (fun h0 : term499 => @lem3929701 m n p h0 h1). Qed.
Lemma lem3929703 (m : nat) (p : nat) (h1 : term508 m p) : term508 m p.
Proof. exact (h1). Qed.
Lemma lem3929704 (m : nat) (p : nat) (h1 : term508 m p) : term507 m p.
Proof. exact (ex_elim (@lem3929703 m p h1) (fun n : nat => fun h0 : term509 m p n => @lem3929702 m n p h0)). Qed.
Lemma lem3929705 (h1 : term499) : term499.
Proof. exact (h1). Qed.
Lemma lem3929706 (m : nat) (p : nat) (h1 : term499) (h2 : term508 m p) : Peano.le m p.
Proof. exact (@lem3929704 m p h2 (@lem3929705 h1)). Qed.
Lemma lem3929707 (m : nat) (p : nat) (h1 : term499) : term510 m p.
Proof. exact (fun h0 : term508 m p => @lem3929706 m p h1 h0). Qed.
Lemma lem3929708 (m : nat) (h1 : term499) : term511 m.
Proof. exact (fun p : nat => @lem3929707 m p h1). Qed.
Lemma lem3929709 (h1 : term499) : term512.
Proof. exact (fun m : nat => @lem3929708 m h1). Qed.
Lemma lem3929710 : term513.
Proof. exact (fun h0 : term499 => @lem3929709 h0). Qed.
Lemma lem3929711 : term512.
Proof. exact (@lem3929710 (@lem93743)). Qed.
Lemma lem3929712 (m : nat) : term514 m.
Proof. exact (@lem3929711 m). Qed.
Lemma lem3929713 (m : nat) : (term514 m) = (term511 m).
Proof. exact (eq_refl (term514 m)). Qed.
Lemma lem3929714 (m : nat) : term511 m.
Proof. exact (EQ_MP (@lem3929713 m) (@lem3929712 m)). Qed.
Lemma lem3929715 (m : nat) (p : nat) : term515 m p.
Proof. exact (@lem3929714 m p). Qed.
Lemma lem3929716 (m : nat) (p : nat) : (term515 m p) = (term510 m p).
Proof. exact (eq_refl (term515 m p)). Qed.
Lemma lem3929718 (t1 : Prop) : term516 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3929719 (t1 : Prop) : (term516 t1) = (term517 t1).
Proof. exact (eq_refl (term516 t1)). Qed.
Lemma lem3929720 (t1 : Prop) : term517 t1.
Proof. exact (EQ_MP (@lem3929719 t1) (@lem3929718 t1)). Qed.
Lemma lem3929721 (t1 : Prop) (t2 : Prop) : term518 t1 t2.
Proof. exact (@lem3929720 t1 t2). Qed.
Lemma lem3929722 (t1 : Prop) (t2 : Prop) : (term518 t1 t2) = (term519 t1 t2).
Proof. exact (eq_refl (term518 t1 t2)). Qed.
Lemma lem3929723 (t1 : Prop) (t2 : Prop) : term519 t1 t2.
Proof. exact (EQ_MP (@lem3929722 t1 t2) (@lem3929721 t1 t2)). Qed.
Lemma lem3929724 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term520 t1 t2 t3.
Proof. exact (@lem3929723 t1 t2 t3). Qed.
Lemma lem3929725 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term520 t1 t2 t3) = ((term521 t1 t2 t3) = (term522 t1 t2 t3)).
Proof. exact (eq_refl (term520 t1 t2 t3)). Qed.
Lemma lem3929726 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term521 t1 t2 t3) = (term522 t1 t2 t3).
Proof. exact (EQ_MP (@lem3929725 t1 t2 t3) (@lem3929724 t1 t2 t3)). Qed.
Lemma lem3929727 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term522 t1 t2 t3) = (term521 t1 t2 t3).
Proof. exact (SYM (@lem3929726 t1 t2 t3)). Qed.
Lemma lem3929731 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term300 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3929732 {_101211 : Type'} (s : _101211 -> Prop) (t : _101211 -> Prop) : (s = t) = (term300 _101211 s t).
Proof. exact (@lem3929731 _101211 s t). Qed.
Lemma lem3929733 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : ((term523 _101211 _101227 a s t) = (term524 _101211 _101227 a s t)) = (term525 _101211 _101227 a s t).
Proof. exact (@lem3929732 _101211 (term523 _101211 _101227 a s t) (term524 _101211 _101227 a s t)). Qed.
Lemma lem3929750 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term525 _101211 _101227 a s t) = ((term523 _101211 _101227 a s t) = (term524 _101211 _101227 a s t)).
Proof. exact (SYM (@lem3929733 _101211 _101227 a s t)). Qed.
Lemma lem3929758 {A : Type'} (s : type686 A) (x : A) : (term526 A x s) = (term527 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3929759 {_101211 : Type'} (s : type686 _101211) (x : _101211) : (term526 _101211 x s) = (term527 _101211 s x).
Proof. exact (@lem3929758 _101211 s x). Qed.
Lemma lem3929760 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term528 _101211 _101227 x a s t) = (term529 _101211 _101227 a s t x).
Proof. exact (@lem3929759 _101211 (term530 _101211 _101227 a s t) x). Qed.
Lemma lem3929770 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term303 _83064 x P) = (term304 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem3929771 {_101211 : Type'} (P : type909 _101211) (x : _101211 -> Prop) : (term531 _101211 x P) = (term532 _101211 P x).
Proof. exact (@lem3929770 (_101211 -> Prop) P x). Qed.
Lemma lem3929772 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) : (term533 _101211 _101227 t' a s t) = (term534 _101211 _101227 a s t t').
Proof. exact (@lem3929771 _101211 (term535 _101211 _101227 a s t) t'). Qed.
Lemma lem3929773 {_101211 _101227 : Type'} (GEN_PVAR_110 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term536 _101211 _101227 a s t GEN_PVAR_110) = (term537 _101211 _101227 GEN_PVAR_110 a s t).
Proof. exact (eq_refl (term536 _101211 _101227 a s t GEN_PVAR_110)). Qed.
Lemma lem3929774 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term538 _101211 _101227 a s t) = (term539 _101211 _101227 a s t).
Proof. exact (fun_ext (fun GEN_PVAR_110 : _101211 -> Prop => @lem3929773 _101211 _101227 GEN_PVAR_110 a s t)). Qed.
Lemma lem3929775 {_101211 : Type'} : (@GSPEC (_101211 -> Prop)) = (@GSPEC (_101211 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_101211 -> Prop))). Qed.
Lemma lem3929776 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term540 _101211 _101227 a s t) = (term530 _101211 _101227 a s t).
Proof. exact (MK_COMB (@lem3929775 _101211) (@lem3929774 _101211 _101227 a s t)). Qed.
Lemma lem3929777 {_101211 : Type'} (t : _101211 -> Prop) : (@IN (_101211 -> Prop) t) = (@IN (_101211 -> Prop) t).
Proof. exact (eq_refl (@IN (_101211 -> Prop) t)). Qed.
Lemma lem3929778 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term533 _101211 _101227 t a s t') = (term541 _101211 _101227 t a s t').
Proof. exact (MK_COMB (@lem3929777 _101211 t) (@lem3929776 _101211 _101227 a s t')). Qed.
Lemma lem3929779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929780 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term542 _101211 _101227 t a s t') = (term543 _101211 _101227 t a s t').
Proof. exact (MK_COMB (@lem3929779) (@lem3929778 _101211 _101227 t a s t')). Qed.
Lemma lem3929781 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term534 _101211 _101227 a s t' t) = (term544 _101211 _101227 t a s t').
Proof. exact (eq_refl (term534 _101211 _101227 a s t' t)). Qed.
Lemma lem3929782 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : ((term533 _101211 _101227 t a s t') = (term534 _101211 _101227 a s t' t)) = ((term541 _101211 _101227 t a s t') = (term544 _101211 _101227 t a s t')).
Proof. exact (MK_COMB (@lem3929780 _101211 _101227 t a s t') (@lem3929781 _101211 _101227 t a s t')). Qed.
Lemma lem3929783 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term541 _101211 _101227 t a s t') = (term544 _101211 _101227 t a s t').
Proof. exact (EQ_MP (@lem3929782 _101211 _101227 t a s t') (@lem3929772 _101211 _101227 a s t' t)). Qed.
Lemma lem3929789 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3929790 {_101211 : Type'} (f : type1527 _101211) (y : Prop) : (term545 _101211 f y) = (f y).
Proof. exact (@lem3929789 Prop (type686 _101211) f y). Qed.
Lemma lem3929791 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (a : _101227) (s : _101227 -> Prop) : (term546 _101211 _101227 t x a s) = (term547 _101211 _101227 t x a s).
Proof. exact (@lem3929790 _101211 (term548 _101211 t) (term549 _101227 x a s)). Qed.
Lemma lem3929792 {_101211 : Type'} (p : Prop) (t : _101211 -> Prop) : (term550 _101211 t p) = (term551 _101211 p t).
Proof. exact (eq_refl (term550 _101211 t p)). Qed.
Lemma lem3929793 {_101211 : Type'} (t : _101211 -> Prop) : (term552 _101211 t) = (term548 _101211 t).
Proof. exact (fun_ext (fun p : Prop => @lem3929792 _101211 p t)). Qed.
Lemma lem3929794 {_101227 : Type'} (x : _101227) (a : _101227) (s : _101227 -> Prop) : (term549 _101227 x a s) = (term549 _101227 x a s).
Proof. exact (eq_refl (term549 _101227 x a s)). Qed.
Lemma lem3929795 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (a : _101227) (s : _101227 -> Prop) : (term546 _101211 _101227 t x a s) = (term547 _101211 _101227 t x a s).
Proof. exact (MK_COMB (@lem3929793 _101211 t) (@lem3929794 _101227 x a s)). Qed.
Lemma lem3929796 {_101211 : Type'} : (@eq ((_101211 -> Prop) -> Prop)) = (@eq ((_101211 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_101211 -> Prop) -> Prop))). Qed.
Lemma lem3929797 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (a : _101227) (s : _101227 -> Prop) : (term553 _101211 _101227 t x a s) = (term554 _101211 _101227 t x a s).
Proof. exact (MK_COMB (@lem3929796 _101211) (@lem3929795 _101211 _101227 t x a s)). Qed.
Lemma lem3929798 {_101211 _101227 : Type'} (x : _101227) (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : (term547 _101211 _101227 t x a s) = (term555 _101211 _101227 x a s t).
Proof. exact (eq_refl (term547 _101211 _101227 t x a s)). Qed.
Lemma lem3929799 {_101211 _101227 : Type'} (x : _101227) (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : ((term546 _101211 _101227 t x a s) = (term547 _101211 _101227 t x a s)) = ((term547 _101211 _101227 t x a s) = (term555 _101211 _101227 x a s t)).
Proof. exact (MK_COMB (@lem3929797 _101211 _101227 t x a s) (@lem3929798 _101211 _101227 x a s t)). Qed.
Lemma lem3929800 {_101211 _101227 : Type'} (x : _101227) (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : (term547 _101211 _101227 t x a s) = (term555 _101211 _101227 x a s t).
Proof. exact (EQ_MP (@lem3929799 _101211 _101227 x a s t) (@lem3929791 _101211 _101227 t x a s)). Qed.
Lemma lem3929804 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3929805 {_101227 : Type'} (y : _101227) (x : _101227) (s : _101227 -> Prop) : (term549 _101227 x y s) = (term556 _101227 y x s).
Proof. exact (@lem3929804 _101227 y x s). Qed.
Lemma lem3929806 {_101227 : Type'} (a : _101227) (x : _101227) (s : _101227 -> Prop) : (term549 _101227 x a s) = (term556 _101227 a x s).
Proof. exact (@lem3929805 _101227 a x s). Qed.
Lemma lem3929812 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3929813 {_101227 : Type'} (P : _101227 -> Prop) (x : _101227) : (@IN _101227 x P) = (P x).
Proof. exact (@lem3929812 _101227 P x). Qed.
Lemma lem3929814 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (@IN _101227 x s) = (s x).
Proof. exact (@lem3929813 _101227 s x). Qed.
Lemma lem3929815 {_101227 : Type'} (x : _101227) (a : _101227) : (term557 _101227 x a) = (term557 _101227 x a).
Proof. exact (eq_refl (term557 _101227 x a)). Qed.
Lemma lem3929816 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term556 _101227 a x s) = (term558 _101227 a s x).
Proof. exact (MK_COMB (@lem3929815 _101227 x a) (@lem3929814 _101227 s x)). Qed.
Lemma lem3929819 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term549 _101227 x a s) = (term558 _101227 a s x).
Proof. exact (TRANS (@lem3929806 _101227 a x s) (@lem3929816 _101227 a s x)). Qed.
Lemma lem3929820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929821 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term559 _101227 x a s) = (term560 _101227 a s x).
Proof. exact (MK_COMB (@lem3929820) (@lem3929819 _101227 a s x)). Qed.
Lemma lem3929824 {_101211 : Type'} (t : _101211 -> Prop) (t' : _101211 -> Prop) : (t = t') = (t = t').
Proof. exact (eq_refl (t = t')). Qed.
Lemma lem3929825 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) (t' : _101211 -> Prop) : (term561 _101211 _101227 x a s t t') = (term562 _101211 _101227 a s x t t').
Proof. exact (MK_COMB (@lem3929821 _101227 a s x) (@lem3929824 _101211 t t')). Qed.
Lemma lem3929828 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term555 _101211 _101227 x a s t) = (term563 _101211 _101227 a s x t).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929825 _101211 _101227 a s x t t')). Qed.
Lemma lem3929829 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term547 _101211 _101227 t x a s) = (term563 _101211 _101227 a s x t).
Proof. exact (TRANS (@lem3929800 _101211 _101227 x a s t) (@lem3929828 _101211 _101227 a s x t)). Qed.
Lemma lem3929830 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3929831 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term564 _101211 _101227 t a s t' x) = (term565 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3929829 _101211 _101227 a s x t) (@lem3929830 _101211 _101227 t' x)). Qed.
Lemma lem3929833 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3929834 {_101211 : Type'} (f : type686 _101211) (y : _101211 -> Prop) : (term566 _101211 f y) = (f y).
Proof. exact (@lem3929833 (_101211 -> Prop) Prop f y). Qed.
Lemma lem3929835 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term567 _101211 _101227 a s t t' x) = (term565 _101211 _101227 a s t t' x).
Proof. exact (@lem3929834 _101211 (term563 _101211 _101227 a s x t) (t' x)). Qed.
Lemma lem3929836 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) (t' : _101211 -> Prop) : (term568 _101211 _101227 a s x t t') = (term562 _101211 _101227 a s x t t').
Proof. exact (eq_refl (term568 _101211 _101227 a s x t t')). Qed.
Lemma lem3929837 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term569 _101211 _101227 a s x t) = (term563 _101211 _101227 a s x t).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929836 _101211 _101227 a s x t t')). Qed.
Lemma lem3929838 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3929839 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term567 _101211 _101227 a s t t' x) = (term565 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3929837 _101211 _101227 a s x t) (@lem3929838 _101211 _101227 t' x)). Qed.
Lemma lem3929840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929841 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term570 _101211 _101227 a s t t' x) = (term571 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3929840) (@lem3929839 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929842 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term565 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term565 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929843 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : ((term567 _101211 _101227 a s t t' x) = (term565 _101211 _101227 a s t t' x)) = ((term565 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3929841 _101211 _101227 a s t t' x) (@lem3929842 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929844 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term565 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3929843 _101211 _101227 a s t t' x) (@lem3929835 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929853 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term564 _101211 _101227 t a s t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (TRANS (@lem3929831 _101211 _101227 a s t t' x) (@lem3929844 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929854 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term573 _101211 _101227 t a s t') = (term574 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3929853 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929855 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3929856 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term544 _101211 _101227 t a s t') = (term575 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3929855 _101227) (@lem3929854 _101211 _101227 a s t t')). Qed.
Lemma lem3929861 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term541 _101211 _101227 t a s t') = (term575 _101211 _101227 a s t t').
Proof. exact (TRANS (@lem3929783 _101211 _101227 t a s t') (@lem3929856 _101211 _101227 a s t t')). Qed.
Lemma lem3929862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929863 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term576 _101211 _101227 t a s t') = (term577 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3929862) (@lem3929861 _101211 _101227 a s t t')). Qed.
Lemma lem3929865 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3929866 {_101211 : Type'} (P : _101211 -> Prop) (x : _101211) : (@IN _101211 x P) = (P x).
Proof. exact (@lem3929865 _101211 P x). Qed.
Lemma lem3929867 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (@IN _101211 x t) = (t x).
Proof. exact (@lem3929866 _101211 t x). Qed.
Lemma lem3929868 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term578 _101211 _101227 a s t x t') = (term579 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3929863 _101211 _101227 a s t' t) (@lem3929867 _101211 t' x)). Qed.
Lemma lem3929871 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term580 _101211 _101227 a s t x) = (term581 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929868 _101211 _101227 a s t t' x)). Qed.
Lemma lem3929872 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3929873 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term529 _101211 _101227 a s t x) = (term582 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3929872 _101211) (@lem3929871 _101211 _101227 a s t x)). Qed.
Lemma lem3929878 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term528 _101211 _101227 x a s t) = (term582 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3929760 _101211 _101227 a s t x) (@lem3929873 _101211 _101227 a s t x)). Qed.
Lemma lem3929879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929880 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term583 _101211 _101227 x a s t) = (term584 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3929879) (@lem3929878 _101211 _101227 a s t x)). Qed.
Lemma lem3929882 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term585 A x s t) = (term586 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3929883 {_101211 : Type'} (s : _101211 -> Prop) (x : _101211) (t : _101211 -> Prop) : (term585 _101211 x s t) = (term586 _101211 s x t).
Proof. exact (@lem3929882 _101211 s x t). Qed.
Lemma lem3929884 {_101211 _101227 : Type'} (a : _101227) (x : _101211) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term587 _101211 _101227 x a s t) = (term588 _101211 _101227 a x s t).
Proof. exact (@lem3929883 _101211 (t a) x (term589 _101211 _101227 s t)). Qed.
Lemma lem3929888 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3929889 {_101211 : Type'} (P : _101211 -> Prop) (x : _101211) : (@IN _101211 x P) = (P x).
Proof. exact (@lem3929888 _101211 P x). Qed.
Lemma lem3929890 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term590 _101211 _101227 x t a) = (t a x).
Proof. exact (@lem3929889 _101211 (t a) x). Qed.
Lemma lem3929891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3929892 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term591 _101211 _101227 x t a) = (term592 _101211 _101227 t a x).
Proof. exact (MK_COMB (@lem3929891) (@lem3929890 _101211 _101227 t a x)). Qed.
Lemma lem3929894 {A : Type'} (s : type686 A) (x : A) : (term526 A x s) = (term527 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3929895 {_101211 : Type'} (s : type686 _101211) (x : _101211) : (term526 _101211 x s) = (term527 _101211 s x).
Proof. exact (@lem3929894 _101211 s x). Qed.
Lemma lem3929896 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term593 _101211 _101227 x s t) = (term594 _101211 _101227 s t x).
Proof. exact (@lem3929895 _101211 (term595 _101211 _101227 s t) x). Qed.
Lemma lem3929906 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term303 _83064 x P) = (term304 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem3929907 {_101211 : Type'} (P : type909 _101211) (x : _101211 -> Prop) : (term531 _101211 x P) = (term532 _101211 P x).
Proof. exact (@lem3929906 (_101211 -> Prop) P x). Qed.
Lemma lem3929908 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) : (term596 _101211 _101227 t' s t) = (term597 _101211 _101227 s t t').
Proof. exact (@lem3929907 _101211 (term598 _101211 _101227 s t) t'). Qed.
Lemma lem3929909 {_101211 _101227 : Type'} (GEN_PVAR_111 : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term599 _101211 _101227 s t GEN_PVAR_111) = (term600 _101211 _101227 GEN_PVAR_111 s t).
Proof. exact (eq_refl (term599 _101211 _101227 s t GEN_PVAR_111)). Qed.
Lemma lem3929910 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term601 _101211 _101227 s t) = (term602 _101211 _101227 s t).
Proof. exact (fun_ext (fun GEN_PVAR_111 : _101211 -> Prop => @lem3929909 _101211 _101227 GEN_PVAR_111 s t)). Qed.
Lemma lem3929911 {_101211 : Type'} : (@GSPEC (_101211 -> Prop)) = (@GSPEC (_101211 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_101211 -> Prop))). Qed.
Lemma lem3929912 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term603 _101211 _101227 s t) = (term595 _101211 _101227 s t).
Proof. exact (MK_COMB (@lem3929911 _101211) (@lem3929910 _101211 _101227 s t)). Qed.
Lemma lem3929913 {_101211 : Type'} (t : _101211 -> Prop) : (@IN (_101211 -> Prop) t) = (@IN (_101211 -> Prop) t).
Proof. exact (eq_refl (@IN (_101211 -> Prop) t)). Qed.
Lemma lem3929914 {_101211 _101227 : Type'} (t : _101211 -> Prop) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term596 _101211 _101227 t s t') = (term604 _101211 _101227 t s t').
Proof. exact (MK_COMB (@lem3929913 _101211 t) (@lem3929912 _101211 _101227 s t')). Qed.
Lemma lem3929915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929916 {_101211 _101227 : Type'} (t : _101211 -> Prop) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term605 _101211 _101227 t s t') = (term606 _101211 _101227 t s t').
Proof. exact (MK_COMB (@lem3929915) (@lem3929914 _101211 _101227 t s t')). Qed.
Lemma lem3929917 {_101211 _101227 : Type'} (t : _101211 -> Prop) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term597 _101211 _101227 s t' t) = (term607 _101211 _101227 t s t').
Proof. exact (eq_refl (term597 _101211 _101227 s t' t)). Qed.
Lemma lem3929918 {_101211 _101227 : Type'} (t : _101211 -> Prop) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : ((term596 _101211 _101227 t s t') = (term597 _101211 _101227 s t' t)) = ((term604 _101211 _101227 t s t') = (term607 _101211 _101227 t s t')).
Proof. exact (MK_COMB (@lem3929916 _101211 _101227 t s t') (@lem3929917 _101211 _101227 t s t')). Qed.
Lemma lem3929919 {_101211 _101227 : Type'} (t : _101211 -> Prop) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) : (term604 _101211 _101227 t s t') = (term607 _101211 _101227 t s t').
Proof. exact (EQ_MP (@lem3929918 _101211 _101227 t s t') (@lem3929908 _101211 _101227 s t' t)). Qed.
Lemma lem3929925 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3929926 {_101211 : Type'} (f : type1527 _101211) (y : Prop) : (term545 _101211 f y) = (f y).
Proof. exact (@lem3929925 Prop (type686 _101211) f y). Qed.
Lemma lem3929927 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (s : _101227 -> Prop) : (term608 _101211 _101227 t x s) = (term609 _101211 _101227 t x s).
Proof. exact (@lem3929926 _101211 (term548 _101211 t) (@IN _101227 x s)). Qed.
Lemma lem3929928 {_101211 : Type'} (p : Prop) (t : _101211 -> Prop) : (term550 _101211 t p) = (term551 _101211 p t).
Proof. exact (eq_refl (term550 _101211 t p)). Qed.
Lemma lem3929929 {_101211 : Type'} (t : _101211 -> Prop) : (term552 _101211 t) = (term548 _101211 t).
Proof. exact (fun_ext (fun p : Prop => @lem3929928 _101211 p t)). Qed.
Lemma lem3929930 {_101227 : Type'} (x : _101227) (s : _101227 -> Prop) : (@IN _101227 x s) = (@IN _101227 x s).
Proof. exact (eq_refl (@IN _101227 x s)). Qed.
Lemma lem3929931 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (s : _101227 -> Prop) : (term608 _101211 _101227 t x s) = (term609 _101211 _101227 t x s).
Proof. exact (MK_COMB (@lem3929929 _101211 t) (@lem3929930 _101227 x s)). Qed.
Lemma lem3929932 {_101211 : Type'} : (@eq ((_101211 -> Prop) -> Prop)) = (@eq ((_101211 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_101211 -> Prop) -> Prop))). Qed.
Lemma lem3929933 {_101211 _101227 : Type'} (t : _101211 -> Prop) (x : _101227) (s : _101227 -> Prop) : (term610 _101211 _101227 t x s) = (term611 _101211 _101227 t x s).
Proof. exact (MK_COMB (@lem3929932 _101211) (@lem3929931 _101211 _101227 t x s)). Qed.
Lemma lem3929934 {_101211 _101227 : Type'} (x : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : (term609 _101211 _101227 t x s) = (term612 _101211 _101227 x s t).
Proof. exact (eq_refl (term609 _101211 _101227 t x s)). Qed.
Lemma lem3929935 {_101211 _101227 : Type'} (x : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : ((term608 _101211 _101227 t x s) = (term609 _101211 _101227 t x s)) = ((term609 _101211 _101227 t x s) = (term612 _101211 _101227 x s t)).
Proof. exact (MK_COMB (@lem3929933 _101211 _101227 t x s) (@lem3929934 _101211 _101227 x s t)). Qed.
Lemma lem3929936 {_101211 _101227 : Type'} (x : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) : (term609 _101211 _101227 t x s) = (term612 _101211 _101227 x s t).
Proof. exact (EQ_MP (@lem3929935 _101211 _101227 x s t) (@lem3929927 _101211 _101227 t x s)). Qed.
Lemma lem3929940 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3929941 {_101227 : Type'} (P : _101227 -> Prop) (x : _101227) : (@IN _101227 x P) = (P x).
Proof. exact (@lem3929940 _101227 P x). Qed.
Lemma lem3929942 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (@IN _101227 x s) = (s x).
Proof. exact (@lem3929941 _101227 s x). Qed.
Lemma lem3929943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929944 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (term328 _101227 x s) = (term329 _101227 s x).
Proof. exact (MK_COMB (@lem3929943) (@lem3929942 _101227 s x)). Qed.
Lemma lem3929947 {_101211 : Type'} (t : _101211 -> Prop) (t' : _101211 -> Prop) : (t = t') = (t = t').
Proof. exact (eq_refl (t = t')). Qed.
Lemma lem3929948 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) (t' : _101211 -> Prop) : (term613 _101211 _101227 x s t t') = (term614 _101211 _101227 s x t t').
Proof. exact (MK_COMB (@lem3929944 _101227 s x) (@lem3929947 _101211 t t')). Qed.
Lemma lem3929951 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term612 _101211 _101227 x s t) = (term615 _101211 _101227 s x t).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929948 _101211 _101227 s x t t')). Qed.
Lemma lem3929952 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term609 _101211 _101227 t x s) = (term615 _101211 _101227 s x t).
Proof. exact (TRANS (@lem3929936 _101211 _101227 x s t) (@lem3929951 _101211 _101227 s x t)). Qed.
Lemma lem3929953 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3929954 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term616 _101211 _101227 t s t' x) = (term617 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3929952 _101211 _101227 s x t) (@lem3929953 _101211 _101227 t' x)). Qed.
Lemma lem3929956 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3929957 {_101211 : Type'} (f : type686 _101211) (y : _101211 -> Prop) : (term566 _101211 f y) = (f y).
Proof. exact (@lem3929956 (_101211 -> Prop) Prop f y). Qed.
Lemma lem3929958 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term618 _101211 _101227 s t t' x) = (term617 _101211 _101227 s t t' x).
Proof. exact (@lem3929957 _101211 (term615 _101211 _101227 s x t) (t' x)). Qed.
Lemma lem3929959 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) (t' : _101211 -> Prop) : (term619 _101211 _101227 s x t t') = (term614 _101211 _101227 s x t t').
Proof. exact (eq_refl (term619 _101211 _101227 s x t t')). Qed.
Lemma lem3929960 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x : _101227) (t : _101211 -> Prop) : (term620 _101211 _101227 s x t) = (term615 _101211 _101227 s x t).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929959 _101211 _101227 s x t t')). Qed.
Lemma lem3929961 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3929962 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term618 _101211 _101227 s t t' x) = (term617 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3929960 _101211 _101227 s x t) (@lem3929961 _101211 _101227 t' x)). Qed.
Lemma lem3929963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3929964 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term621 _101211 _101227 s t t' x) = (term622 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3929963) (@lem3929962 _101211 _101227 s t t' x)). Qed.
Lemma lem3929965 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term617 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term617 _101211 _101227 s t t' x)). Qed.
Lemma lem3929966 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : ((term618 _101211 _101227 s t t' x) = (term617 _101211 _101227 s t t' x)) = ((term617 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x)).
Proof. exact (MK_COMB (@lem3929964 _101211 _101227 s t t' x) (@lem3929965 _101211 _101227 s t t' x)). Qed.
Lemma lem3929967 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term617 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (EQ_MP (@lem3929966 _101211 _101227 s t t' x) (@lem3929958 _101211 _101227 s t t' x)). Qed.
Lemma lem3929972 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term616 _101211 _101227 t s t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (TRANS (@lem3929954 _101211 _101227 s t t' x) (@lem3929967 _101211 _101227 s t t' x)). Qed.
Lemma lem3929973 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term624 _101211 _101227 t s t') = (term625 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3929972 _101211 _101227 s t t' x)). Qed.
Lemma lem3929974 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3929975 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term607 _101211 _101227 t s t') = (term626 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3929974 _101227) (@lem3929973 _101211 _101227 s t t')). Qed.
Lemma lem3929980 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term604 _101211 _101227 t s t') = (term626 _101211 _101227 s t t').
Proof. exact (TRANS (@lem3929919 _101211 _101227 t s t') (@lem3929975 _101211 _101227 s t t')). Qed.
Lemma lem3929981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3929982 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term627 _101211 _101227 t s t') = (term628 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3929981) (@lem3929980 _101211 _101227 s t t')). Qed.
Lemma lem3929984 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3929985 {_101211 : Type'} (P : _101211 -> Prop) (x : _101211) : (@IN _101211 x P) = (P x).
Proof. exact (@lem3929984 _101211 P x). Qed.
Lemma lem3929986 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (@IN _101211 x t) = (t x).
Proof. exact (@lem3929985 _101211 t x). Qed.
Lemma lem3929987 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term629 _101211 _101227 s t x t') = (term630 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3929982 _101211 _101227 s t' t) (@lem3929986 _101211 t' x)). Qed.
Lemma lem3929990 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term631 _101211 _101227 s t x) = (term632 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3929987 _101211 _101227 s t t' x)). Qed.
Lemma lem3929991 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3929992 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term594 _101211 _101227 s t x) = (term633 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3929991 _101211) (@lem3929990 _101211 _101227 s t x)). Qed.
Lemma lem3929997 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term593 _101211 _101227 x s t) = (term633 _101211 _101227 s t x).
Proof. exact (TRANS (@lem3929896 _101211 _101227 s t x) (@lem3929992 _101211 _101227 s t x)). Qed.
Lemma lem3929998 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term588 _101211 _101227 a x s t) = (term634 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3929892 _101211 _101227 t a x) (@lem3929997 _101211 _101227 s t x)). Qed.
Lemma lem3930001 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term587 _101211 _101227 x a s t) = (term634 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3929884 _101211 _101227 a x s t) (@lem3929998 _101211 _101227 a s t x)). Qed.
Lemma lem3930002 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term528 _101211 _101227 x a s t) = (term587 _101211 _101227 x a s t)) = ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3929880 _101211 _101227 a s t x) (@lem3930001 _101211 _101227 a s t x)). Qed.
Lemma lem3930005 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term635 _101211 _101227 a s t) = (term636 _101211 _101227 a s t).
Proof. exact (fun_ext (fun x : _101211 => @lem3930002 _101211 _101227 a s t x)). Qed.
Lemma lem3930006 {_101211 : Type'} : (@all _101211) = (@all _101211).
Proof. exact (eq_refl (@all _101211)). Qed.
Lemma lem3930007 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term525 _101211 _101227 a s t) = (term637 _101211 _101227 a s t).
Proof. exact (MK_COMB (@lem3930006 _101211) (@lem3930005 _101211 _101227 a s t)). Qed.
Lemma lem3930012 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term637 _101211 _101227 a s t) = (term525 _101211 _101227 a s t).
Proof. exact (SYM (@lem3930007 _101211 _101227 a s t)). Qed.
Lemma lem3930014 (p : Prop) : p = (term357 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3930015 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term637 _101211 _101227 a s t) = (term638 _101211 _101227 a s t).
Proof. exact (@lem3930014 (term637 _101211 _101227 a s t)). Qed.
Lemma lem3930016 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term638 _101211 _101227 a s t) = (term637 _101211 _101227 a s t).
Proof. exact (SYM (@lem3930015 _101211 _101227 a s t)). Qed.
Lemma lem3930017 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term639 _101211 _101227 a s t) : term639 _101211 _101227 a s t.
Proof. exact (h1). Qed.
Lemma lem3930020 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term638 _101211 _101227 a s t) : term638 _101211 _101227 a s t.
Proof. exact (h1). Qed.
Lemma lem3930021 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term640 _101211 _101227 a s t.
Proof. exact (fun h0 : term638 _101211 _101227 a s t => @lem3930020 _101211 _101227 a s t h0). Qed.
Lemma lem3930022 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term640 _101211 _101227 a s t) : term640 _101211 _101227 a s t.
Proof. exact (h1). Qed.
Lemma lem3930023 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term638 _101211 _101227 a s t) : term638 _101211 _101227 a s t.
Proof. exact (h1). Qed.
Lemma lem3930024 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term638 _101211 _101227 a s t) (h2 : term640 _101211 _101227 a s t) : term638 _101211 _101227 a s t.
Proof. exact (@lem3930022 _101211 _101227 a s t h2 (@lem3930023 _101211 _101227 a s t h1)). Qed.
Lemma lem3930025 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term638 _101211 _101227 a s t) : term641 _101211 _101227 a s t.
Proof. exact (fun h0 : term640 _101211 _101227 a s t => @lem3930024 _101211 _101227 a s t h1 h0). Qed.
Lemma lem3930026 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term640 _101211 _101227 a s t) : term640 _101211 _101227 a s t.
Proof. exact (h1). Qed.
Lemma lem3930027 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term638 _101211 _101227 a s t) (h2 : term640 _101211 _101227 a s t) : term638 _101211 _101227 a s t.
Proof. exact (@lem3930025 _101211 _101227 a s t h1 (@lem3930026 _101211 _101227 a s t h2)). Qed.
Lemma lem3930028 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term640 _101211 _101227 a s t) : term640 _101211 _101227 a s t.
Proof. exact (fun h0 : term638 _101211 _101227 a s t => @lem3930027 _101211 _101227 a s t h0 h1). Qed.
Lemma lem3930029 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term642 _101211 _101227 a s t.
Proof. exact (fun h0 : term640 _101211 _101227 a s t => @lem3930028 _101211 _101227 a s t h0). Qed.
Lemma lem3930032 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term640 _101211 _101227 a s t.
Proof. exact (@lem3930029 _101211 _101227 a s t (@lem3930021 _101211 _101227 a s t)). Qed.
Lemma lem3930033 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term640 _101211 _101227 a s t.
Proof. exact (@lem3930032 _101211 _101227 a s t). Qed.
Lemma lem3930047 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3930048 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term638 _101211 _101227 a s t) = (term643 _101211 _101227 a s t).
Proof. exact (@lem3930047 (term639 _101211 _101227 a s t)). Qed.
Lemma lem3930050 (t : Prop) : (term122 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3930051 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term643 _101211 _101227 a s t) = (term637 _101211 _101227 a s t).
Proof. exact (@lem3930050 (term637 _101211 _101227 a s t)). Qed.
Lemma lem3930056 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term638 _101211 _101227 a s t) = (term637 _101211 _101227 a s t).
Proof. exact (TRANS (@lem3930048 _101211 _101227 a s t) (@lem3930051 _101211 _101227 a s t)). Qed.
Lemma lem3930241 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term644 _101211 _101227 s t) = (term645 _101211 _101227 s t).
Proof. exact (fun_ext (fun a : _101227 => @lem3930056 _101211 _101227 a s t)). Qed.
Lemma lem3930242 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3930243 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term646 _101211 _101227 s t) = (term647 _101211 _101227 s t).
Proof. exact (MK_COMB (@lem3930242 _101227) (@lem3930241 _101211 _101227 s t)). Qed.
Lemma lem3930248 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : (term648 _101211 _101227 t) = (term649 _101211 _101227 t).
Proof. exact (fun_ext (fun s : _101227 -> Prop => @lem3930243 _101211 _101227 s t)). Qed.
Lemma lem3930249 {_101227 : Type'} : (@all (_101227 -> Prop)) = (@all (_101227 -> Prop)).
Proof. exact (eq_refl (@all (_101227 -> Prop))). Qed.
Lemma lem3930250 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : (term650 _101211 _101227 t) = (term651 _101211 _101227 t).
Proof. exact (MK_COMB (@lem3930249 _101227) (@lem3930248 _101211 _101227 t)). Qed.
Lemma lem3930255 {_101211 _101227 : Type'} : (term652 _101211 _101227) = (term653 _101211 _101227).
Proof. exact (fun_ext (fun t : type1470 _101211 _101227 => @lem3930250 _101211 _101227 t)). Qed.
Lemma lem3930256 {_101211 _101227 : Type'} : (@all (_101227 -> _101211 -> Prop)) = (@all (_101227 -> _101211 -> Prop)).
Proof. exact (eq_refl (@all (_101227 -> _101211 -> Prop))). Qed.
Lemma lem3930265 {_101211 _101227 : Type'} : (term654 _101211 _101227) = (term655 _101211 _101227).
Proof. exact (MK_COMB (@lem3930256 _101211 _101227) (@lem3930255 _101211 _101227)). Qed.
Lemma lem3930266 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930271 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term623 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term623 _101211 _101227 s t t' x)). Qed.
Lemma lem3930272 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term625 _101211 _101227 s t t') = (term625 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930271 _101211 _101227 s t t' x)). Qed.
Lemma lem3930273 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930274 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term626 _101211 _101227 s t t') = (term626 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930273 _101227) (@lem3930272 _101211 _101227 s t t')). Qed.
Lemma lem3930275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930276 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term628 _101211 _101227 s t t') = (term628 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930275) (@lem3930274 _101211 _101227 s t t')). Qed.
Lemma lem3930277 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term630 _101211 _101227 s t t' x) = (term630 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930276 _101211 _101227 s t' t) (@lem3930266 _101211 t' x)). Qed.
Lemma lem3930278 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term632 _101211 _101227 s t x) = (term632 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930277 _101211 _101227 s t t' x)). Qed.
Lemma lem3930279 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930280 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term633 _101211 _101227 s t x) = (term633 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3930279 _101211) (@lem3930278 _101211 _101227 s t x)). Qed.
Lemma lem3930283 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3930284 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term634 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930283 _101211 _101227 t a x) (@lem3930280 _101211 _101227 s t x)). Qed.
Lemma lem3930285 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930294 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term572 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term572 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930295 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term574 _101211 _101227 a s t t') = (term574 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930294 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930296 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930297 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term575 _101211 _101227 a s t t') = (term575 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930296 _101227) (@lem3930295 _101211 _101227 a s t t')). Qed.
Lemma lem3930298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930299 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term577 _101211 _101227 a s t t') = (term577 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930298) (@lem3930297 _101211 _101227 a s t t')). Qed.
Lemma lem3930300 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term579 _101211 _101227 a s t t' x) = (term579 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930299 _101211 _101227 a s t' t) (@lem3930285 _101211 t' x)). Qed.
Lemma lem3930301 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term581 _101211 _101227 a s t x) = (term581 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930300 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930302 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930303 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term582 _101211 _101227 a s t x) = (term582 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930302 _101211) (@lem3930301 _101211 _101227 a s t x)). Qed.
Lemma lem3930304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3930305 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term584 _101211 _101227 a s t x) = (term584 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930304) (@lem3930303 _101211 _101227 a s t x)). Qed.
Lemma lem3930306 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x)) = ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3930305 _101211 _101227 a s t x) (@lem3930284 _101211 _101227 a s t x)). Qed.
Lemma lem3930307 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term636 _101211 _101227 a s t) = (term636 _101211 _101227 a s t).
Proof. exact (fun_ext (fun x : _101211 => @lem3930306 _101211 _101227 a s t x)). Qed.
Lemma lem3930308 {_101211 : Type'} : (@all _101211) = (@all _101211).
Proof. exact (eq_refl (@all _101211)). Qed.
Lemma lem3930309 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term637 _101211 _101227 a s t) = (term637 _101211 _101227 a s t).
Proof. exact (MK_COMB (@lem3930308 _101211) (@lem3930307 _101211 _101227 a s t)). Qed.
Lemma lem3930310 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term645 _101211 _101227 s t) = (term645 _101211 _101227 s t).
Proof. exact (fun_ext (fun a : _101227 => @lem3930309 _101211 _101227 a s t)). Qed.
Lemma lem3930311 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3930312 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term647 _101211 _101227 s t) = (term647 _101211 _101227 s t).
Proof. exact (MK_COMB (@lem3930311 _101227) (@lem3930310 _101211 _101227 s t)). Qed.
Lemma lem3930313 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : (term649 _101211 _101227 t) = (term649 _101211 _101227 t).
Proof. exact (fun_ext (fun s : _101227 -> Prop => @lem3930312 _101211 _101227 s t)). Qed.
Lemma lem3930314 {_101227 : Type'} : (@all (_101227 -> Prop)) = (@all (_101227 -> Prop)).
Proof. exact (eq_refl (@all (_101227 -> Prop))). Qed.
Lemma lem3930315 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : (term651 _101211 _101227 t) = (term651 _101211 _101227 t).
Proof. exact (MK_COMB (@lem3930314 _101227) (@lem3930313 _101211 _101227 t)). Qed.
Lemma lem3930316 {_101211 _101227 : Type'} : (term653 _101211 _101227) = (term653 _101211 _101227).
Proof. exact (fun_ext (fun t : type1470 _101211 _101227 => @lem3930315 _101211 _101227 t)). Qed.
Lemma lem3930317 {_101211 _101227 : Type'} : (@all (_101227 -> _101211 -> Prop)) = (@all (_101227 -> _101211 -> Prop)).
Proof. exact (eq_refl (@all (_101227 -> _101211 -> Prop))). Qed.
Lemma lem3930318 {_101211 _101227 : Type'} : (term655 _101211 _101227) = (term655 _101211 _101227).
Proof. exact (MK_COMB (@lem3930317 _101211 _101227) (@lem3930316 _101211 _101227)). Qed.
Lemma lem3930381 {_101211 _101227 : Type'} : (term654 _101211 _101227) = (term655 _101211 _101227).
Proof. exact (TRANS (@lem3930265 _101211 _101227) (@lem3930318 _101211 _101227)). Qed.
Lemma lem3930382 {_101211 _101227 : Type'} : (term655 _101211 _101227) = (term654 _101211 _101227).
Proof. exact (SYM (@lem3930381 _101211 _101227)). Qed.
Lemma lem3930384 (p : Prop) : p = (term357 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3930385 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x)) = (term656 _101211 _101227 a s t x).
Proof. exact (@lem3930384 ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x))). Qed.
Lemma lem3930386 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term656 _101211 _101227 a s t x) = ((term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x)).
Proof. exact (SYM (@lem3930385 _101211 _101227 a s t x)). Qed.
Lemma lem3930387 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term657 _101211 _101227 a s t x) : term657 _101211 _101227 a s t x.
Proof. exact (h1). Qed.
Lemma lem3930396 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term658 _101227 a s x) = (term659 _101227 a s x).
Proof. exact (@lem17160 (x = a) (s x)). Qed.
Lemma lem3930400 {_101211 _101227 : Type'} (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term660 _101211 _101227 t t' x) = (term660 _101211 _101227 t t' x).
Proof. exact (eq_refl (term660 _101211 _101227 t t' x)). Qed.
Lemma lem3930402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3930403 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term661 _101227 a s x) = (term662 _101227 a s x).
Proof. exact (MK_COMB (@lem3930402) (@lem3930396 _101227 a s x)). Qed.
Lemma lem3930404 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term663 _101211 _101227 a s t t' x) = (term664 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930403 _101227 a s x) (@lem3930400 _101211 _101227 t t' x)). Qed.
Lemma lem3930405 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term665 _101211 _101227 a s t t' x) = (term663 _101211 _101227 a s t t' x).
Proof. exact (@lem17045 (term558 _101227 a s x) (t = (t' x))). Qed.
Lemma lem3930406 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term665 _101211 _101227 a s t t' x) = (term664 _101211 _101227 a s t t' x).
Proof. exact (TRANS (@lem3930405 _101211 _101227 a s t t' x) (@lem3930404 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930409 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term572 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term572 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930410 {_101227 : Type'} (P : _101227 -> Prop) : (term376 _101227 P) = (term377 _101227 P).
Proof. exact (@lem18394 _101227 P). Qed.
Lemma lem3930411 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term666 _101211 _101227 a s t t') = (term667 _101211 _101227 a s t t').
Proof. exact (@lem3930410 _101227 (term574 _101211 _101227 a s t t')). Qed.
Lemma lem3930412 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term668 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term668 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3930414 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term669 _101211 _101227 a s t t' x) = (term665 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930413) (@lem3930412 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930415 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term669 _101211 _101227 a s t t' x) = (term664 _101211 _101227 a s t t' x).
Proof. exact (TRANS (@lem3930414 _101211 _101227 a s t t' x) (@lem3930406 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930416 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term670 _101211 _101227 a s t t') = (term671 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930415 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930417 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3930418 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term667 _101211 _101227 a s t t') = (term672 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930417 _101227) (@lem3930416 _101211 _101227 a s t t')). Qed.
Lemma lem3930419 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term666 _101211 _101227 a s t t') = (term672 _101211 _101227 a s t t').
Proof. exact (TRANS (@lem3930411 _101211 _101227 a s t t') (@lem3930418 _101211 _101227 a s t t')). Qed.
Lemma lem3930420 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term574 _101211 _101227 a s t t') = (term574 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930409 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930421 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930422 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term575 _101211 _101227 a s t t') = (term575 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930421 _101227) (@lem3930420 _101211 _101227 a s t t')). Qed.
Lemma lem3930423 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term474 _101211 t x) = (term474 _101211 t x).
Proof. exact (eq_refl (term474 _101211 t x)). Qed.
Lemma lem3930424 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3930426 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term673 _101211 _101227 a s t t') = (term674 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930425) (@lem3930419 _101211 _101227 a s t t')). Qed.
Lemma lem3930427 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term675 _101211 _101227 a s t t' x) = (term676 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930426 _101211 _101227 a s t' t) (@lem3930423 _101211 t' x)). Qed.
Lemma lem3930428 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term677 _101211 _101227 a s t t' x) = (term675 _101211 _101227 a s t t' x).
Proof. exact (@lem17045 (term575 _101211 _101227 a s t' t) (t' x)). Qed.
Lemma lem3930429 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term677 _101211 _101227 a s t t' x) = (term676 _101211 _101227 a s t t' x).
Proof. exact (TRANS (@lem3930428 _101211 _101227 a s t t' x) (@lem3930427 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930431 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term577 _101211 _101227 a s t t') = (term577 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930430) (@lem3930422 _101211 _101227 a s t t')). Qed.
Lemma lem3930432 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term579 _101211 _101227 a s t t' x) = (term579 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930431 _101211 _101227 a s t' t) (@lem3930424 _101211 t' x)). Qed.
Lemma lem3930433 {_101211 : Type'} (P : type686 _101211) : (term678 _101211 P) = (term679 _101211 P).
Proof. exact (@lem18394 (_101211 -> Prop) P). Qed.
Lemma lem3930434 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term680 _101211 _101227 a s t x) = (term681 _101211 _101227 a s t x).
Proof. exact (@lem3930433 _101211 (term581 _101211 _101227 a s t x)). Qed.
Lemma lem3930435 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term682 _101211 _101227 a s t x t') = (term579 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term682 _101211 _101227 a s t x t')). Qed.
Lemma lem3930436 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3930437 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term683 _101211 _101227 a s t x t') = (term677 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930436) (@lem3930435 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930438 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term683 _101211 _101227 a s t x t') = (term676 _101211 _101227 a s t t' x).
Proof. exact (TRANS (@lem3930437 _101211 _101227 a s t t' x) (@lem3930429 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930439 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term684 _101211 _101227 a s t x) = (term685 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930438 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930440 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3930441 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term681 _101211 _101227 a s t x) = (term686 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930440 _101211) (@lem3930439 _101211 _101227 a s t x)). Qed.
Lemma lem3930442 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term680 _101211 _101227 a s t x) = (term686 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930434 _101211 _101227 a s t x) (@lem3930441 _101211 _101227 a s t x)). Qed.
Lemma lem3930443 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term581 _101211 _101227 a s t x) = (term581 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930432 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930444 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930445 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term582 _101211 _101227 a s t x) = (term582 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930444 _101211) (@lem3930443 _101211 _101227 a s t x)). Qed.
Lemma lem3930456 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term687 _101211 _101227 s t t' x) = (term688 _101211 _101227 s t t' x).
Proof. exact (@lem17045 (s x) (t = (t' x))). Qed.
Lemma lem3930459 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term623 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term623 _101211 _101227 s t t' x)). Qed.
Lemma lem3930460 {_101227 : Type'} (P : _101227 -> Prop) : (term376 _101227 P) = (term377 _101227 P).
Proof. exact (@lem18394 _101227 P). Qed.
Lemma lem3930461 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term689 _101211 _101227 s t t') = (term690 _101211 _101227 s t t').
Proof. exact (@lem3930460 _101227 (term625 _101211 _101227 s t t')). Qed.
Lemma lem3930462 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term691 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term691 _101211 _101227 s t t' x)). Qed.
Lemma lem3930463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3930464 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term692 _101211 _101227 s t t' x) = (term687 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930463) (@lem3930462 _101211 _101227 s t t' x)). Qed.
Lemma lem3930465 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term692 _101211 _101227 s t t' x) = (term688 _101211 _101227 s t t' x).
Proof. exact (TRANS (@lem3930464 _101211 _101227 s t t' x) (@lem3930456 _101211 _101227 s t t' x)). Qed.
Lemma lem3930466 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term693 _101211 _101227 s t t') = (term694 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930465 _101211 _101227 s t t' x)). Qed.
Lemma lem3930467 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3930468 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term690 _101211 _101227 s t t') = (term695 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930467 _101227) (@lem3930466 _101211 _101227 s t t')). Qed.
Lemma lem3930469 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term689 _101211 _101227 s t t') = (term695 _101211 _101227 s t t').
Proof. exact (TRANS (@lem3930461 _101211 _101227 s t t') (@lem3930468 _101211 _101227 s t t')). Qed.
Lemma lem3930470 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term625 _101211 _101227 s t t') = (term625 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930459 _101211 _101227 s t t' x)). Qed.
Lemma lem3930471 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930472 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term626 _101211 _101227 s t t') = (term626 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930471 _101227) (@lem3930470 _101211 _101227 s t t')). Qed.
Lemma lem3930473 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term474 _101211 t x) = (term474 _101211 t x).
Proof. exact (eq_refl (term474 _101211 t x)). Qed.
Lemma lem3930474 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3930476 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term696 _101211 _101227 s t t') = (term697 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930475) (@lem3930469 _101211 _101227 s t t')). Qed.
Lemma lem3930477 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term698 _101211 _101227 s t t' x) = (term699 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930476 _101211 _101227 s t' t) (@lem3930473 _101211 t' x)). Qed.
Lemma lem3930478 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term700 _101211 _101227 s t t' x) = (term698 _101211 _101227 s t t' x).
Proof. exact (@lem17045 (term626 _101211 _101227 s t' t) (t' x)). Qed.
Lemma lem3930479 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term700 _101211 _101227 s t t' x) = (term699 _101211 _101227 s t t' x).
Proof. exact (TRANS (@lem3930478 _101211 _101227 s t t' x) (@lem3930477 _101211 _101227 s t t' x)). Qed.
Lemma lem3930480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930481 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term628 _101211 _101227 s t t') = (term628 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930480) (@lem3930472 _101211 _101227 s t t')). Qed.
Lemma lem3930482 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term630 _101211 _101227 s t t' x) = (term630 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930481 _101211 _101227 s t' t) (@lem3930474 _101211 t' x)). Qed.
Lemma lem3930483 {_101211 : Type'} (P : type686 _101211) : (term678 _101211 P) = (term679 _101211 P).
Proof. exact (@lem18394 (_101211 -> Prop) P). Qed.
Lemma lem3930484 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term701 _101211 _101227 s t x) = (term702 _101211 _101227 s t x).
Proof. exact (@lem3930483 _101211 (term632 _101211 _101227 s t x)). Qed.
Lemma lem3930485 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term703 _101211 _101227 s t x t') = (term630 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term703 _101211 _101227 s t x t')). Qed.
Lemma lem3930486 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3930487 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term704 _101211 _101227 s t x t') = (term700 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930486) (@lem3930485 _101211 _101227 s t t' x)). Qed.
Lemma lem3930488 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term704 _101211 _101227 s t x t') = (term699 _101211 _101227 s t t' x).
Proof. exact (TRANS (@lem3930487 _101211 _101227 s t t' x) (@lem3930479 _101211 _101227 s t t' x)). Qed.
Lemma lem3930489 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term705 _101211 _101227 s t x) = (term706 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930488 _101211 _101227 s t t' x)). Qed.
Lemma lem3930490 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3930491 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term702 _101211 _101227 s t x) = (term707 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3930490 _101211) (@lem3930489 _101211 _101227 s t x)). Qed.
Lemma lem3930492 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term701 _101211 _101227 s t x) = (term707 _101211 _101227 s t x).
Proof. exact (TRANS (@lem3930484 _101211 _101227 s t x) (@lem3930491 _101211 _101227 s t x)). Qed.
Lemma lem3930493 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term632 _101211 _101227 s t x) = (term632 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930482 _101211 _101227 s t t' x)). Qed.
Lemma lem3930494 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930495 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term633 _101211 _101227 s t x) = (term633 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3930494 _101211) (@lem3930493 _101211 _101227 s t x)). Qed.
Lemma lem3930497 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term708 _101211 _101227 t a x) = (term708 _101211 _101227 t a x).
Proof. exact (eq_refl (term708 _101211 _101227 t a x)). Qed.
Lemma lem3930498 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term709 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930497 _101211 _101227 t a x) (@lem3930492 _101211 _101227 s t x)). Qed.
Lemma lem3930499 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term711 _101211 _101227 a s t x) = (term709 _101211 _101227 a s t x).
Proof. exact (@lem17160 (t a x) (term633 _101211 _101227 s t x)). Qed.
Lemma lem3930500 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term711 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930499 _101211 _101227 a s t x) (@lem3930498 _101211 _101227 a s t x)). Qed.
Lemma lem3930502 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3930503 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term634 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930502 _101211 _101227 t a x) (@lem3930495 _101211 _101227 s t x)). Qed.
Lemma lem3930504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930505 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term712 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930504) (@lem3930442 _101211 _101227 a s t x)). Qed.
Lemma lem3930506 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term714 _101211 _101227 a s t x) = (term715 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930505 _101211 _101227 a s t x) (@lem3930503 _101211 _101227 a s t x)). Qed.
Lemma lem3930507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930508 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term716 _101211 _101227 a s t x) = (term716 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930507) (@lem3930445 _101211 _101227 a s t x)). Qed.
Lemma lem3930509 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term717 _101211 _101227 a s t x) = (term718 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930508 _101211 _101227 a s t x) (@lem3930500 _101211 _101227 a s t x)). Qed.
Lemma lem3930510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3930511 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term719 _101211 _101227 a s t x) = (term720 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930510) (@lem3930509 _101211 _101227 a s t x)). Qed.
Lemma lem3930512 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term721 _101211 _101227 a s t x) = (term722 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930511 _101211 _101227 a s t x) (@lem3930506 _101211 _101227 a s t x)). Qed.
Lemma lem3930513 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term657 _101211 _101227 a s t x) = (term721 _101211 _101227 a s t x).
Proof. exact (@lem17646 (term582 _101211 _101227 a s t x) (term634 _101211 _101227 a s t x)). Qed.
Lemma lem3930514 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term657 _101211 _101227 a s t x) = (term722 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930513 _101211 _101227 a s t x) (@lem3930512 _101211 _101227 a s t x)). Qed.
Lemma lem3930881 {A : Type'} (P : A -> Prop) (Q : Prop) : (term405 A P Q) = (term406 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3930882 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term405 _101227 P Q) = (term406 _101227 P Q).
Proof. exact (@lem3930881 _101227 P Q). Qed.
Lemma lem3930883 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term723 _101211 _101227 a s t t' x) = (term724 _101211 _101227 a s t t' x).
Proof. exact (@lem3930882 _101227 (term574 _101211 _101227 a s t' t) (t' x)). Qed.
Lemma lem3930884 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term668 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term668 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930885 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term725 _101211 _101227 a s t t') = (term574 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930884 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930886 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930887 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term726 _101211 _101227 a s t t') = (term575 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930886 _101227) (@lem3930885 _101211 _101227 a s t t')). Qed.
Lemma lem3930888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930889 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term727 _101211 _101227 a s t t') = (term577 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3930888) (@lem3930887 _101211 _101227 a s t t')). Qed.
Lemma lem3930890 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930891 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term723 _101211 _101227 a s t t' x) = (term579 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930889 _101211 _101227 a s t' t) (@lem3930890 _101211 t' x)). Qed.
Lemma lem3930892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3930893 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term728 _101211 _101227 a s t t' x) = (term729 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930892) (@lem3930891 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930894 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term668 _101211 _101227 a s t t' x) = (term572 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term668 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930896 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term730 _101211 _101227 a s t t' x) = (term731 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930895) (@lem3930894 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930897 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930898 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term732 _101211 _101227 a s t x t' x') = (term733 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3930896 _101211 _101227 a s t' t x) (@lem3930897 _101211 t' x')). Qed.
Lemma lem3930899 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term734 _101211 _101227 a s t t' x) = (term735 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3930898 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3930900 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930901 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term724 _101211 _101227 a s t t' x) = (term736 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930900 _101227) (@lem3930899 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930902 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term723 _101211 _101227 a s t t' x) = (term724 _101211 _101227 a s t t' x)) = ((term579 _101211 _101227 a s t t' x) = (term736 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3930893 _101211 _101227 a s t t' x) (@lem3930901 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930903 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term579 _101211 _101227 a s t t' x) = (term736 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3930902 _101211 _101227 a s t t' x) (@lem3930883 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930904 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term581 _101211 _101227 a s t x) = (term737 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930903 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930905 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930906 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term582 _101211 _101227 a s t x) = (term738 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930905 _101211) (@lem3930904 _101211 _101227 a s t x)). Qed.
Lemma lem3930907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930908 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term716 _101211 _101227 a s t x) = (term739 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930907) (@lem3930906 _101211 _101227 a s t x)). Qed.
Lemma lem3930909 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (eq_refl (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930910 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term718 _101211 _101227 a s t x) = (term740 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930908 _101211 _101227 a s t x) (@lem3930909 _101211 _101227 a s t x)). Qed.
Lemma lem3930912 {A : Type'} (P : A -> Prop) (Q : Prop) : (term405 A P Q) = (term406 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3930913 {_101211 : Type'} (P : type686 _101211) (Q : Prop) : (term741 _101211 P Q) = (term742 _101211 P Q).
Proof. exact (@lem3930912 (_101211 -> Prop) P Q). Qed.
Lemma lem3930914 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term743 _101211 _101227 a s t x) = (term744 _101211 _101227 a s t x).
Proof. exact (@lem3930913 _101211 (term737 _101211 _101227 a s t x) (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930915 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term745 _101211 _101227 a s t x t') = (term736 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term745 _101211 _101227 a s t x t')). Qed.
Lemma lem3930916 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term746 _101211 _101227 a s t x) = (term737 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930915 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930917 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930918 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term747 _101211 _101227 a s t x) = (term738 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930917 _101211) (@lem3930916 _101211 _101227 a s t x)). Qed.
Lemma lem3930919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930920 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term748 _101211 _101227 a s t x) = (term739 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930919) (@lem3930918 _101211 _101227 a s t x)). Qed.
Lemma lem3930921 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (eq_refl (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930922 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term743 _101211 _101227 a s t x) = (term740 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930920 _101211 _101227 a s t x) (@lem3930921 _101211 _101227 a s t x)). Qed.
Lemma lem3930923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3930924 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term749 _101211 _101227 a s t x) = (term750 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930923) (@lem3930922 _101211 _101227 a s t x)). Qed.
Lemma lem3930925 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term745 _101211 _101227 a s t x t') = (term736 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term745 _101211 _101227 a s t x t')). Qed.
Lemma lem3930926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930927 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term751 _101211 _101227 a s t x t') = (term752 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930926) (@lem3930925 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930928 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (eq_refl (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930929 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term753 _101211 _101227 t a s t' x) = (term754 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3930927 _101211 _101227 a s t' t x) (@lem3930928 _101211 _101227 a s t' x)). Qed.
Lemma lem3930930 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term755 _101211 _101227 a s t x) = (term756 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930929 _101211 _101227 t' a s t x)). Qed.
Lemma lem3930931 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930932 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term744 _101211 _101227 a s t x) = (term757 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930931 _101211) (@lem3930930 _101211 _101227 a s t x)). Qed.
Lemma lem3930933 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term743 _101211 _101227 a s t x) = (term744 _101211 _101227 a s t x)) = ((term740 _101211 _101227 a s t x) = (term757 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3930924 _101211 _101227 a s t x) (@lem3930932 _101211 _101227 a s t x)). Qed.
Lemma lem3930934 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term740 _101211 _101227 a s t x) = (term757 _101211 _101227 a s t x).
Proof. exact (EQ_MP (@lem3930933 _101211 _101227 a s t x) (@lem3930914 _101211 _101227 a s t x)). Qed.
Lemma lem3930936 {A : Type'} (P : A -> Prop) (Q : Prop) : (term405 A P Q) = (term406 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3930937 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term405 _101227 P Q) = (term406 _101227 P Q).
Proof. exact (@lem3930936 _101227 P Q). Qed.
Lemma lem3930938 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term758 _101211 _101227 t a s t' x) = (term759 _101211 _101227 t a s t' x).
Proof. exact (@lem3930937 _101227 (term735 _101211 _101227 a s t' t x) (term710 _101211 _101227 a s t' x)). Qed.
Lemma lem3930939 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term760 _101211 _101227 a s t t' x' x) = (term733 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term760 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3930940 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term761 _101211 _101227 a s t t' x) = (term735 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3930939 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3930941 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930942 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term762 _101211 _101227 a s t t' x) = (term736 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930941 _101227) (@lem3930940 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930944 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term763 _101211 _101227 a s t t' x) = (term752 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3930943) (@lem3930942 _101211 _101227 a s t t' x)). Qed.
Lemma lem3930945 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (eq_refl (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930946 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term758 _101211 _101227 t a s t' x) = (term754 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3930944 _101211 _101227 a s t' t x) (@lem3930945 _101211 _101227 a s t' x)). Qed.
Lemma lem3930947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3930948 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term764 _101211 _101227 t a s t' x) = (term765 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3930947) (@lem3930946 _101211 _101227 t a s t' x)). Qed.
Lemma lem3930949 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term760 _101211 _101227 a s t t' x' x) = (term733 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term760 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3930950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930951 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term766 _101211 _101227 a s t t' x' x) = (term767 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3930950) (@lem3930949 _101211 _101227 a s t x t' x')). Qed.
Lemma lem3930952 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term710 _101211 _101227 a s t x).
Proof. exact (eq_refl (term710 _101211 _101227 a s t x)). Qed.
Lemma lem3930953 {_101211 _101227 : Type'} (x : _101227) (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x' : _101211) : (term768 _101211 _101227 t x a s t' x') = (term769 _101211 _101227 x t a s t' x').
Proof. exact (MK_COMB (@lem3930951 _101211 _101227 a s t' x t x') (@lem3930952 _101211 _101227 a s t' x')). Qed.
Lemma lem3930954 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term770 _101211 _101227 t a s t' x) = (term771 _101211 _101227 t a s t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3930953 _101211 _101227 x' t a s t' x)). Qed.
Lemma lem3930955 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930956 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term759 _101211 _101227 t a s t' x) = (term772 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3930955 _101227) (@lem3930954 _101211 _101227 t a s t' x)). Qed.
Lemma lem3930957 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : ((term758 _101211 _101227 t a s t' x) = (term759 _101211 _101227 t a s t' x)) = ((term754 _101211 _101227 t a s t' x) = (term772 _101211 _101227 t a s t' x)).
Proof. exact (MK_COMB (@lem3930948 _101211 _101227 t a s t' x) (@lem3930956 _101211 _101227 t a s t' x)). Qed.
Lemma lem3930958 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term754 _101211 _101227 t a s t' x) = (term772 _101211 _101227 t a s t' x).
Proof. exact (EQ_MP (@lem3930957 _101211 _101227 t a s t' x) (@lem3930938 _101211 _101227 t a s t' x)). Qed.
Lemma lem3930959 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term756 _101211 _101227 a s t x) = (term773 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930958 _101211 _101227 t' a s t x)). Qed.
Lemma lem3930960 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930961 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term757 _101211 _101227 a s t x) = (term774 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930960 _101211) (@lem3930959 _101211 _101227 a s t x)). Qed.
Lemma lem3930962 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term740 _101211 _101227 a s t x) = (term774 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930934 _101211 _101227 a s t x) (@lem3930961 _101211 _101227 a s t x)). Qed.
Lemma lem3930963 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term718 _101211 _101227 a s t x) = (term774 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930910 _101211 _101227 a s t x) (@lem3930962 _101211 _101227 a s t x)). Qed.
Lemma lem3930964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3930965 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term720 _101211 _101227 a s t x) = (term775 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930964) (@lem3930963 _101211 _101227 a s t x)). Qed.
Lemma lem3930967 {A : Type'} (P : A -> Prop) (Q : Prop) : (term405 A P Q) = (term406 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3930968 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term405 _101227 P Q) = (term406 _101227 P Q).
Proof. exact (@lem3930967 _101227 P Q). Qed.
Lemma lem3930969 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term776 _101211 _101227 s t t' x) = (term777 _101211 _101227 s t t' x).
Proof. exact (@lem3930968 _101227 (term625 _101211 _101227 s t' t) (t' x)). Qed.
Lemma lem3930970 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term691 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term691 _101211 _101227 s t t' x)). Qed.
Lemma lem3930971 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term778 _101211 _101227 s t t') = (term625 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3930970 _101211 _101227 s t t' x)). Qed.
Lemma lem3930972 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930973 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term779 _101211 _101227 s t t') = (term626 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930972 _101227) (@lem3930971 _101211 _101227 s t t')). Qed.
Lemma lem3930974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930975 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term780 _101211 _101227 s t t') = (term628 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3930974) (@lem3930973 _101211 _101227 s t t')). Qed.
Lemma lem3930976 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930977 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term776 _101211 _101227 s t t' x) = (term630 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930975 _101211 _101227 s t' t) (@lem3930976 _101211 t' x)). Qed.
Lemma lem3930978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3930979 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term781 _101211 _101227 s t t' x) = (term782 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930978) (@lem3930977 _101211 _101227 s t t' x)). Qed.
Lemma lem3930980 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term691 _101211 _101227 s t t' x) = (term623 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term691 _101211 _101227 s t t' x)). Qed.
Lemma lem3930981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3930982 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term783 _101211 _101227 s t t' x) = (term784 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930981) (@lem3930980 _101211 _101227 s t t' x)). Qed.
Lemma lem3930983 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3930984 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term785 _101211 _101227 s t x t' x') = (term786 _101211 _101227 s t x t' x').
Proof. exact (MK_COMB (@lem3930982 _101211 _101227 s t' t x) (@lem3930983 _101211 t' x')). Qed.
Lemma lem3930985 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term787 _101211 _101227 s t t' x) = (term788 _101211 _101227 s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3930984 _101211 _101227 s t x' t' x)). Qed.
Lemma lem3930986 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3930987 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term777 _101211 _101227 s t t' x) = (term789 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3930986 _101227) (@lem3930985 _101211 _101227 s t t' x)). Qed.
Lemma lem3930988 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term776 _101211 _101227 s t t' x) = (term777 _101211 _101227 s t t' x)) = ((term630 _101211 _101227 s t t' x) = (term789 _101211 _101227 s t t' x)).
Proof. exact (MK_COMB (@lem3930979 _101211 _101227 s t t' x) (@lem3930987 _101211 _101227 s t t' x)). Qed.
Lemma lem3930989 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term630 _101211 _101227 s t t' x) = (term789 _101211 _101227 s t t' x).
Proof. exact (EQ_MP (@lem3930988 _101211 _101227 s t t' x) (@lem3930969 _101211 _101227 s t t' x)). Qed.
Lemma lem3930990 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term632 _101211 _101227 s t x) = (term790 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930989 _101211 _101227 s t t' x)). Qed.
Lemma lem3930991 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3930992 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term633 _101211 _101227 s t x) = (term791 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3930991 _101211) (@lem3930990 _101211 _101227 s t x)). Qed.
Lemma lem3930993 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3930994 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term634 _101211 _101227 a s t x) = (term792 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930993 _101211 _101227 t a x) (@lem3930992 _101211 _101227 s t x)). Qed.
Lemma lem3930996 {A : Type'} (P : Prop) (Q : A -> Prop) : (term793 A P Q) = (term794 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3930997 {_101211 : Type'} (P : Prop) (Q : type686 _101211) : (term795 _101211 P Q) = (term796 _101211 P Q).
Proof. exact (@lem3930996 (_101211 -> Prop) P Q). Qed.
Lemma lem3930998 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term797 _101211 _101227 a s t x) = (term798 _101211 _101227 a s t x).
Proof. exact (@lem3930997 _101211 (t a x) (term790 _101211 _101227 s t x)). Qed.
Lemma lem3930999 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term799 _101211 _101227 s t x t') = (term789 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term799 _101211 _101227 s t x t')). Qed.
Lemma lem3931000 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term800 _101211 _101227 s t x) = (term790 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3930999 _101211 _101227 s t t' x)). Qed.
Lemma lem3931001 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931002 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term801 _101211 _101227 s t x) = (term791 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3931001 _101211) (@lem3931000 _101211 _101227 s t x)). Qed.
Lemma lem3931003 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3931004 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term797 _101211 _101227 a s t x) = (term792 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931003 _101211 _101227 t a x) (@lem3931002 _101211 _101227 s t x)). Qed.
Lemma lem3931005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931006 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term802 _101211 _101227 a s t x) = (term803 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931005) (@lem3931004 _101211 _101227 a s t x)). Qed.
Lemma lem3931007 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term799 _101211 _101227 s t x t') = (term789 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term799 _101211 _101227 s t x t')). Qed.
Lemma lem3931008 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3931009 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term804 _101211 _101227 a s t x t') = (term805 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931008 _101211 _101227 t a x) (@lem3931007 _101211 _101227 s t t' x)). Qed.
Lemma lem3931010 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term806 _101211 _101227 a s t x) = (term807 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931009 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931011 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931012 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term798 _101211 _101227 a s t x) = (term808 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931011 _101211) (@lem3931010 _101211 _101227 a s t x)). Qed.
Lemma lem3931013 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term797 _101211 _101227 a s t x) = (term798 _101211 _101227 a s t x)) = ((term792 _101211 _101227 a s t x) = (term808 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3931006 _101211 _101227 a s t x) (@lem3931012 _101211 _101227 a s t x)). Qed.
Lemma lem3931014 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term792 _101211 _101227 a s t x) = (term808 _101211 _101227 a s t x).
Proof. exact (EQ_MP (@lem3931013 _101211 _101227 a s t x) (@lem3930998 _101211 _101227 a s t x)). Qed.
Lemma lem3931016 {A : Type'} (P : Prop) (Q : A -> Prop) : (term793 A P Q) = (term794 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3931017 {_101227 : Type'} (P : Prop) (Q : _101227 -> Prop) : (term793 _101227 P Q) = (term794 _101227 P Q).
Proof. exact (@lem3931016 _101227 P Q). Qed.
Lemma lem3931018 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term809 _101211 _101227 a s t t' x) = (term810 _101211 _101227 a s t t' x).
Proof. exact (@lem3931017 _101227 (t a x) (term788 _101211 _101227 s t t' x)). Qed.
Lemma lem3931019 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term811 _101211 _101227 s t t' x' x) = (term786 _101211 _101227 s t x t' x').
Proof. exact (eq_refl (term811 _101211 _101227 s t t' x' x)). Qed.
Lemma lem3931020 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term812 _101211 _101227 s t t' x) = (term788 _101211 _101227 s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931019 _101211 _101227 s t x' t' x)). Qed.
Lemma lem3931021 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931022 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term813 _101211 _101227 s t t' x) = (term789 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931021 _101227) (@lem3931020 _101211 _101227 s t t' x)). Qed.
Lemma lem3931023 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3931024 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term809 _101211 _101227 a s t t' x) = (term805 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931023 _101211 _101227 t a x) (@lem3931022 _101211 _101227 s t t' x)). Qed.
Lemma lem3931025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931026 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term814 _101211 _101227 a s t t' x) = (term815 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931025) (@lem3931024 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931027 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term811 _101211 _101227 s t t' x' x) = (term786 _101211 _101227 s t x t' x').
Proof. exact (eq_refl (term811 _101211 _101227 s t t' x' x)). Qed.
Lemma lem3931028 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term592 _101211 _101227 t a x).
Proof. exact (eq_refl (term592 _101211 _101227 t a x)). Qed.
Lemma lem3931029 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term816 _101211 _101227 a s t t' x' x) = (term817 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931028 _101211 _101227 t a x') (@lem3931027 _101211 _101227 s t x t' x')). Qed.
Lemma lem3931030 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term818 _101211 _101227 a s t t' x) = (term819 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931029 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931031 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931032 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term810 _101211 _101227 a s t t' x) = (term820 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931031 _101227) (@lem3931030 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931033 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term809 _101211 _101227 a s t t' x) = (term810 _101211 _101227 a s t t' x)) = ((term805 _101211 _101227 a s t t' x) = (term820 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3931026 _101211 _101227 a s t t' x) (@lem3931032 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931034 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term805 _101211 _101227 a s t t' x) = (term820 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3931033 _101211 _101227 a s t t' x) (@lem3931018 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931035 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term807 _101211 _101227 a s t x) = (term821 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931034 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931036 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931037 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term808 _101211 _101227 a s t x) = (term822 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931036 _101211) (@lem3931035 _101211 _101227 a s t x)). Qed.
Lemma lem3931038 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term792 _101211 _101227 a s t x) = (term822 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931014 _101211 _101227 a s t x) (@lem3931037 _101211 _101227 a s t x)). Qed.
Lemma lem3931039 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term634 _101211 _101227 a s t x) = (term822 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930994 _101211 _101227 a s t x) (@lem3931038 _101211 _101227 a s t x)). Qed.
Lemma lem3931040 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (eq_refl (term713 _101211 _101227 a s t x)). Qed.
Lemma lem3931041 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term715 _101211 _101227 a s t x) = (term823 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931040 _101211 _101227 a s t x) (@lem3931039 _101211 _101227 a s t x)). Qed.
Lemma lem3931043 {A : Type'} (P : Prop) (Q : A -> Prop) : (term422 A P Q) = (term423 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3931044 {_101211 : Type'} (P : Prop) (Q : type686 _101211) : (term824 _101211 P Q) = (term825 _101211 P Q).
Proof. exact (@lem3931043 (_101211 -> Prop) P Q). Qed.
Lemma lem3931045 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term826 _101211 _101227 a s t x) = (term827 _101211 _101227 a s t x).
Proof. exact (@lem3931044 _101211 (term686 _101211 _101227 a s t x) (term821 _101211 _101227 a s t x)). Qed.
Lemma lem3931046 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term828 _101211 _101227 a s t x t') = (term820 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term828 _101211 _101227 a s t x t')). Qed.
Lemma lem3931047 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term829 _101211 _101227 a s t x) = (term821 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931046 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931048 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931049 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term830 _101211 _101227 a s t x) = (term822 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931048 _101211) (@lem3931047 _101211 _101227 a s t x)). Qed.
Lemma lem3931050 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (eq_refl (term713 _101211 _101227 a s t x)). Qed.
Lemma lem3931051 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term826 _101211 _101227 a s t x) = (term823 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931050 _101211 _101227 a s t x) (@lem3931049 _101211 _101227 a s t x)). Qed.
Lemma lem3931052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931053 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term831 _101211 _101227 a s t x) = (term832 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931052) (@lem3931051 _101211 _101227 a s t x)). Qed.
Lemma lem3931054 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term828 _101211 _101227 a s t x t') = (term820 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term828 _101211 _101227 a s t x t')). Qed.
Lemma lem3931055 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (eq_refl (term713 _101211 _101227 a s t x)). Qed.
Lemma lem3931056 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term833 _101211 _101227 a s t x t') = (term834 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931055 _101211 _101227 a s t x) (@lem3931054 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931057 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term835 _101211 _101227 a s t x) = (term836 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931056 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931058 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931059 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term827 _101211 _101227 a s t x) = (term837 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931058 _101211) (@lem3931057 _101211 _101227 a s t x)). Qed.
Lemma lem3931060 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term826 _101211 _101227 a s t x) = (term827 _101211 _101227 a s t x)) = ((term823 _101211 _101227 a s t x) = (term837 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3931053 _101211 _101227 a s t x) (@lem3931059 _101211 _101227 a s t x)). Qed.
Lemma lem3931061 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term823 _101211 _101227 a s t x) = (term837 _101211 _101227 a s t x).
Proof. exact (EQ_MP (@lem3931060 _101211 _101227 a s t x) (@lem3931045 _101211 _101227 a s t x)). Qed.
Lemma lem3931063 {A : Type'} (P : Prop) (Q : A -> Prop) : (term422 A P Q) = (term423 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3931064 {_101227 : Type'} (P : Prop) (Q : _101227 -> Prop) : (term422 _101227 P Q) = (term423 _101227 P Q).
Proof. exact (@lem3931063 _101227 P Q). Qed.
Lemma lem3931065 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term838 _101211 _101227 a s t t' x) = (term839 _101211 _101227 a s t t' x).
Proof. exact (@lem3931064 _101227 (term686 _101211 _101227 a s t x) (term819 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931066 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term840 _101211 _101227 a s t t' x' x) = (term817 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term840 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3931067 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term841 _101211 _101227 a s t t' x) = (term819 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931066 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931068 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931069 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term842 _101211 _101227 a s t t' x) = (term820 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931068 _101227) (@lem3931067 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931070 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (eq_refl (term713 _101211 _101227 a s t x)). Qed.
Lemma lem3931071 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term838 _101211 _101227 a s t t' x) = (term834 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931070 _101211 _101227 a s t x) (@lem3931069 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931073 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term843 _101211 _101227 a s t t' x) = (term844 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931072) (@lem3931071 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931074 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term840 _101211 _101227 a s t t' x' x) = (term817 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term840 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3931075 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term713 _101211 _101227 a s t x).
Proof. exact (eq_refl (term713 _101211 _101227 a s t x)). Qed.
Lemma lem3931076 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term845 _101211 _101227 a s t t' x' x) = (term846 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931075 _101211 _101227 a s t x') (@lem3931074 _101211 _101227 a s t x t' x')). Qed.
Lemma lem3931077 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term847 _101211 _101227 a s t t' x) = (term848 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931076 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931078 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931079 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term839 _101211 _101227 a s t t' x) = (term849 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931078 _101227) (@lem3931077 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931080 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term838 _101211 _101227 a s t t' x) = (term839 _101211 _101227 a s t t' x)) = ((term834 _101211 _101227 a s t t' x) = (term849 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3931073 _101211 _101227 a s t t' x) (@lem3931079 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931081 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term834 _101211 _101227 a s t t' x) = (term849 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3931080 _101211 _101227 a s t t' x) (@lem3931065 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931082 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term836 _101211 _101227 a s t x) = (term850 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931081 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931083 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931084 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term837 _101211 _101227 a s t x) = (term851 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931083 _101211) (@lem3931082 _101211 _101227 a s t x)). Qed.
Lemma lem3931085 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term823 _101211 _101227 a s t x) = (term851 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931061 _101211 _101227 a s t x) (@lem3931084 _101211 _101227 a s t x)). Qed.
Lemma lem3931086 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term715 _101211 _101227 a s t x) = (term851 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931041 _101211 _101227 a s t x) (@lem3931085 _101211 _101227 a s t x)). Qed.
Lemma lem3931087 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term722 _101211 _101227 a s t x) = (term852 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3930965 _101211 _101227 a s t x) (@lem3931086 _101211 _101227 a s t x)). Qed.
Lemma lem3931089 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term436 A P Q) = (term437 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3931090 {_101211 : Type'} (P : type686 _101211) (Q : type686 _101211) : (term853 _101211 P Q) = (term854 _101211 P Q).
Proof. exact (@lem3931089 (_101211 -> Prop) P Q). Qed.
Lemma lem3931091 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term855 _101211 _101227 a s t x) = (term856 _101211 _101227 a s t x).
Proof. exact (@lem3931090 _101211 (term773 _101211 _101227 a s t x) (term850 _101211 _101227 a s t x)). Qed.
Lemma lem3931092 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term857 _101211 _101227 a s t' x t) = (term772 _101211 _101227 t a s t' x).
Proof. exact (eq_refl (term857 _101211 _101227 a s t' x t)). Qed.
Lemma lem3931093 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term858 _101211 _101227 a s t x) = (term773 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931092 _101211 _101227 t' a s t x)). Qed.
Lemma lem3931094 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931095 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term859 _101211 _101227 a s t x) = (term774 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931094 _101211) (@lem3931093 _101211 _101227 a s t x)). Qed.
Lemma lem3931096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931097 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term860 _101211 _101227 a s t x) = (term775 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931096) (@lem3931095 _101211 _101227 a s t x)). Qed.
Lemma lem3931098 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term861 _101211 _101227 a s t x t') = (term849 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term861 _101211 _101227 a s t x t')). Qed.
Lemma lem3931099 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term862 _101211 _101227 a s t x) = (term850 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931098 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931100 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931101 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term863 _101211 _101227 a s t x) = (term851 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931100 _101211) (@lem3931099 _101211 _101227 a s t x)). Qed.
Lemma lem3931102 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term855 _101211 _101227 a s t x) = (term852 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931097 _101211 _101227 a s t x) (@lem3931101 _101211 _101227 a s t x)). Qed.
Lemma lem3931103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931104 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term864 _101211 _101227 a s t x) = (term865 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931103) (@lem3931102 _101211 _101227 a s t x)). Qed.
Lemma lem3931105 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term857 _101211 _101227 a s t' x t) = (term772 _101211 _101227 t a s t' x).
Proof. exact (eq_refl (term857 _101211 _101227 a s t' x t)). Qed.
Lemma lem3931106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931107 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term866 _101211 _101227 a s t' x t) = (term867 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3931106) (@lem3931105 _101211 _101227 t a s t' x)). Qed.
Lemma lem3931108 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term861 _101211 _101227 a s t x t') = (term849 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term861 _101211 _101227 a s t x t')). Qed.
Lemma lem3931109 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term868 _101211 _101227 a s t x t') = (term869 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931107 _101211 _101227 t' a s t x) (@lem3931108 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931110 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term870 _101211 _101227 a s t x) = (term871 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931109 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931111 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931112 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term856 _101211 _101227 a s t x) = (term872 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931111 _101211) (@lem3931110 _101211 _101227 a s t x)). Qed.
Lemma lem3931113 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : ((term855 _101211 _101227 a s t x) = (term856 _101211 _101227 a s t x)) = ((term852 _101211 _101227 a s t x) = (term872 _101211 _101227 a s t x)).
Proof. exact (MK_COMB (@lem3931104 _101211 _101227 a s t x) (@lem3931112 _101211 _101227 a s t x)). Qed.
Lemma lem3931114 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term852 _101211 _101227 a s t x) = (term872 _101211 _101227 a s t x).
Proof. exact (EQ_MP (@lem3931113 _101211 _101227 a s t x) (@lem3931091 _101211 _101227 a s t x)). Qed.
Lemma lem3931116 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term436 A P Q) = (term437 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3931117 {_101227 : Type'} (P : _101227 -> Prop) (Q : _101227 -> Prop) : (term436 _101227 P Q) = (term437 _101227 P Q).
Proof. exact (@lem3931116 _101227 P Q). Qed.
Lemma lem3931118 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term873 _101211 _101227 a s t t' x) = (term874 _101211 _101227 a s t t' x).
Proof. exact (@lem3931117 _101227 (term771 _101211 _101227 t' a s t x) (term848 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931119 {_101211 _101227 : Type'} (x : _101227) (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x' : _101211) : (term875 _101211 _101227 t a s t' x' x) = (term769 _101211 _101227 x t a s t' x').
Proof. exact (eq_refl (term875 _101211 _101227 t a s t' x' x)). Qed.
Lemma lem3931120 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term876 _101211 _101227 t a s t' x) = (term771 _101211 _101227 t a s t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931119 _101211 _101227 x' t a s t' x)). Qed.
Lemma lem3931121 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931122 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term877 _101211 _101227 t a s t' x) = (term772 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3931121 _101227) (@lem3931120 _101211 _101227 t a s t' x)). Qed.
Lemma lem3931123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931124 {_101211 _101227 : Type'} (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x : _101211) : (term878 _101211 _101227 t a s t' x) = (term867 _101211 _101227 t a s t' x).
Proof. exact (MK_COMB (@lem3931123) (@lem3931122 _101211 _101227 t a s t' x)). Qed.
Lemma lem3931125 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term879 _101211 _101227 a s t t' x' x) = (term846 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term879 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3931126 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term880 _101211 _101227 a s t t' x) = (term848 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931125 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931127 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931128 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term881 _101211 _101227 a s t t' x) = (term849 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931127 _101227) (@lem3931126 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931129 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term873 _101211 _101227 a s t t' x) = (term869 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931124 _101211 _101227 t' a s t x) (@lem3931128 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931131 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term882 _101211 _101227 a s t t' x) = (term883 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931130) (@lem3931129 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931132 {_101211 _101227 : Type'} (x : _101227) (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x' : _101211) : (term875 _101211 _101227 t a s t' x' x) = (term769 _101211 _101227 x t a s t' x').
Proof. exact (eq_refl (term875 _101211 _101227 t a s t' x' x)). Qed.
Lemma lem3931133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931134 {_101211 _101227 : Type'} (x : _101227) (t : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t' : type1470 _101211 _101227) (x' : _101211) : (term884 _101211 _101227 t a s t' x' x) = (term885 _101211 _101227 x t a s t' x').
Proof. exact (MK_COMB (@lem3931133) (@lem3931132 _101211 _101227 x t a s t' x')). Qed.
Lemma lem3931135 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term879 _101211 _101227 a s t t' x' x) = (term846 _101211 _101227 a s t x t' x').
Proof. exact (eq_refl (term879 _101211 _101227 a s t t' x' x)). Qed.
Lemma lem3931136 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term886 _101211 _101227 a s t t' x' x) = (term887 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931134 _101211 _101227 x t' a s t x') (@lem3931135 _101211 _101227 a s t x t' x')). Qed.
Lemma lem3931137 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term888 _101211 _101227 a s t t' x) = (term889 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931136 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931138 {_101227 : Type'} : (@ex _101227) = (@ex _101227).
Proof. exact (eq_refl (@ex _101227)). Qed.
Lemma lem3931139 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term874 _101211 _101227 a s t t' x) = (term890 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931138 _101227) (@lem3931137 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931140 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term873 _101211 _101227 a s t t' x) = (term874 _101211 _101227 a s t t' x)) = ((term869 _101211 _101227 a s t t' x) = (term890 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3931131 _101211 _101227 a s t t' x) (@lem3931139 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931141 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term869 _101211 _101227 a s t t' x) = (term890 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3931140 _101211 _101227 a s t t' x) (@lem3931118 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931142 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term871 _101211 _101227 a s t x) = (term891 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931141 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931143 {_101211 : Type'} : (@ex (_101211 -> Prop)) = (@ex (_101211 -> Prop)).
Proof. exact (eq_refl (@ex (_101211 -> Prop))). Qed.
Lemma lem3931144 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term872 _101211 _101227 a s t x) = (term892 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931143 _101211) (@lem3931142 _101211 _101227 a s t x)). Qed.
Lemma lem3931145 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term852 _101211 _101227 a s t x) = (term892 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931114 _101211 _101227 a s t x) (@lem3931144 _101211 _101227 a s t x)). Qed.
Lemma lem3931147 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term722 _101211 _101227 a s t x) = (term892 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931087 _101211 _101227 a s t x) (@lem3931145 _101211 _101227 a s t x)). Qed.
Lemma lem3931148 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term657 _101211 _101227 a s t x) = (term892 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3930514 _101211 _101227 a s t x) (@lem3931147 _101211 _101227 a s t x)). Qed.
Lemma lem3931149 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term657 _101211 _101227 a s t x) : term892 _101211 _101227 a s t x.
Proof. exact (EQ_MP (@lem3931148 _101211 _101227 a s t x) (@lem3930387 _101211 _101227 a s t x h1)). Qed.
Lemma lem3931150 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term890 _101211 _101227 a s t t' x) : term890 _101211 _101227 a s t t' x.
Proof. exact (h1). Qed.
Lemma lem3931151 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term887 _101211 _101227 a s t x' t' x) : term887 _101211 _101227 a s t x' t' x.
Proof. exact (h1). Qed.
Lemma lem3931156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931157 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931156 _101211 Prop f x). Qed.
Lemma lem3931159 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (t' x) = (@I (_101211 -> Prop) t' x).
Proof. exact (@lem3931157 _101211 t' x). Qed.
Lemma lem3931166 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931167 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931166 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931169 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (@lem3931167 _101211 _101227 t x'). Qed.
Lemma lem3931170 {_101211 : Type'} (t' : _101211 -> Prop) : (@eq (_101211 -> Prop) t') = (@eq (_101211 -> Prop) t').
Proof. exact (eq_refl (@eq (_101211 -> Prop) t')). Qed.
Lemma lem3931171 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (t' = (t x')) = (t' = (@I (_101227 -> _101211 -> Prop) t x')).
Proof. exact (MK_COMB (@lem3931170 _101211 t') (@lem3931169 _101211 _101227 t x')). Qed.
Lemma lem3931176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931177 {_101227 : Type'} (f : _101227 -> Prop) (x : _101227) : (f x) = (@I (_101227 -> Prop) f x).
Proof. exact (@lem3931176 _101227 Prop f x). Qed.
Lemma lem3931179 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) : (s x') = (@I (_101227 -> Prop) s x').
Proof. exact (@lem3931177 _101227 s x'). Qed.
Lemma lem3931180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931181 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) : (term329 _101227 s x') = (term893 _101227 s x').
Proof. exact (MK_COMB (@lem3931180) (@lem3931179 _101227 s x')). Qed.
Lemma lem3931182 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term623 _101211 _101227 s t' t x') = (term894 _101211 _101227 s t' t x').
Proof. exact (MK_COMB (@lem3931181 _101227 s x') (@lem3931171 _101211 _101227 t' t x')). Qed.
Lemma lem3931183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931184 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term784 _101211 _101227 s t' t x') = (term895 _101211 _101227 s t' t x').
Proof. exact (MK_COMB (@lem3931183) (@lem3931182 _101211 _101227 s t' t x')). Qed.
Lemma lem3931185 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term786 _101211 _101227 s t x' t' x) = (term896 _101211 _101227 s t x' t' x).
Proof. exact (MK_COMB (@lem3931184 _101211 _101227 s t' t x') (@lem3931159 _101211 t' x)). Qed.
Lemma lem3931192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931193 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931192 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931194 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : (t a) = (@I (_101227 -> _101211 -> Prop) t a).
Proof. exact (@lem3931193 _101211 _101227 t a). Qed.
Lemma lem3931195 {_101211 : Type'} (x : _101211) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3931196 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (t a x) = (@I (_101227 -> _101211 -> Prop) t a x).
Proof. exact (MK_COMB (@lem3931194 _101211 _101227 t a) (@lem3931195 _101211 x)). Qed.
Lemma lem3931198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931199 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931198 _101211 Prop f x). Qed.
Lemma lem3931200 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (@I (_101227 -> _101211 -> Prop) t a x) = (term897 _101211 _101227 t a x).
Proof. exact (@lem3931199 _101211 (@I (_101227 -> _101211 -> Prop) t a) x). Qed.
Lemma lem3931202 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (t a x) = (term897 _101211 _101227 t a x).
Proof. exact (TRANS (@lem3931196 _101211 _101227 t a x) (@lem3931200 _101211 _101227 t a x)). Qed.
Lemma lem3931203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931204 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term592 _101211 _101227 t a x) = (term898 _101211 _101227 t a x).
Proof. exact (MK_COMB (@lem3931203) (@lem3931202 _101211 _101227 t a x)). Qed.
Lemma lem3931205 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term817 _101211 _101227 a s t x' t' x) = (term899 _101211 _101227 a s t x' t' x).
Proof. exact (MK_COMB (@lem3931204 _101211 _101227 t a x) (@lem3931185 _101211 _101227 s t x' t' x)). Qed.
Lemma lem3931206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931212 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931211 _101211 Prop f x). Qed.
Lemma lem3931214 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (@I (_101211 -> Prop) t x).
Proof. exact (@lem3931212 _101211 t x). Qed.
Lemma lem3931215 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term474 _101211 t x) = (term900 _101211 t x).
Proof. exact (MK_COMB (@lem3931206) (@lem3931214 _101211 t x)). Qed.
Lemma lem3931216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931224 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931223 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931226 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (@I (_101227 -> _101211 -> Prop) t x).
Proof. exact (@lem3931224 _101211 _101227 t x). Qed.
Lemma lem3931227 {_101211 : Type'} (t : _101211 -> Prop) : (@eq (_101211 -> Prop) t) = (@eq (_101211 -> Prop) t).
Proof. exact (eq_refl (@eq (_101211 -> Prop) t)). Qed.
Lemma lem3931228 {_101211 _101227 : Type'} (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (t = (t' x)) = (t = (@I (_101227 -> _101211 -> Prop) t' x)).
Proof. exact (MK_COMB (@lem3931227 _101211 t) (@lem3931226 _101211 _101227 t' x)). Qed.
Lemma lem3931229 {_101211 _101227 : Type'} (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term660 _101211 _101227 t t' x) = (term901 _101211 _101227 t t' x).
Proof. exact (MK_COMB (@lem3931216) (@lem3931228 _101211 _101227 t t' x)). Qed.
Lemma lem3931230 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931236 {_101227 : Type'} (f : _101227 -> Prop) (x : _101227) : (f x) = (@I (_101227 -> Prop) f x).
Proof. exact (@lem3931235 _101227 Prop f x). Qed.
Lemma lem3931238 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (s x) = (@I (_101227 -> Prop) s x).
Proof. exact (@lem3931236 _101227 s x). Qed.
Lemma lem3931239 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (term474 _101227 s x) = (term900 _101227 s x).
Proof. exact (MK_COMB (@lem3931230) (@lem3931238 _101227 s x)). Qed.
Lemma lem3931248 {_101227 : Type'} (x : _101227) (a : _101227) : (term902 _101227 x a) = (term902 _101227 x a).
Proof. exact (eq_refl (term902 _101227 x a)). Qed.
Lemma lem3931249 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term659 _101227 a s x) = (term903 _101227 a s x).
Proof. exact (MK_COMB (@lem3931248 _101227 x a) (@lem3931239 _101227 s x)). Qed.
Lemma lem3931250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931251 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x : _101227) : (term662 _101227 a s x) = (term904 _101227 a s x).
Proof. exact (MK_COMB (@lem3931250) (@lem3931249 _101227 a s x)). Qed.
Lemma lem3931252 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term664 _101211 _101227 a s t t' x) = (term905 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931251 _101227 a s x) (@lem3931229 _101211 _101227 t t' x)). Qed.
Lemma lem3931253 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term671 _101211 _101227 a s t t') = (term906 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3931252 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931254 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931255 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term672 _101211 _101227 a s t t') = (term907 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931254 _101227) (@lem3931253 _101211 _101227 a s t t')). Qed.
Lemma lem3931256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931257 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term674 _101211 _101227 a s t t') = (term908 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931256) (@lem3931255 _101211 _101227 a s t t')). Qed.
Lemma lem3931258 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term676 _101211 _101227 a s t t' x) = (term909 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931257 _101211 _101227 a s t' t) (@lem3931215 _101211 t' x)). Qed.
Lemma lem3931259 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term685 _101211 _101227 a s t x) = (term910 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931258 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931260 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931261 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term686 _101211 _101227 a s t x) = (term911 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931260 _101211) (@lem3931259 _101211 _101227 a s t x)). Qed.
Lemma lem3931262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931263 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term713 _101211 _101227 a s t x) = (term912 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931262) (@lem3931261 _101211 _101227 a s t x)). Qed.
Lemma lem3931264 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term846 _101211 _101227 a s t x' t' x) = (term913 _101211 _101227 a s t x' t' x).
Proof. exact (MK_COMB (@lem3931263 _101211 _101227 a s t x) (@lem3931205 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931271 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931270 _101211 Prop f x). Qed.
Lemma lem3931273 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (t x) = (@I (_101211 -> Prop) t x).
Proof. exact (@lem3931271 _101211 t x). Qed.
Lemma lem3931274 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term474 _101211 t x) = (term900 _101211 t x).
Proof. exact (MK_COMB (@lem3931265) (@lem3931273 _101211 t x)). Qed.
Lemma lem3931275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931282 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931283 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931282 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931285 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x : _101227) : (t x) = (@I (_101227 -> _101211 -> Prop) t x).
Proof. exact (@lem3931283 _101211 _101227 t x). Qed.
Lemma lem3931286 {_101211 : Type'} (t : _101211 -> Prop) : (@eq (_101211 -> Prop) t) = (@eq (_101211 -> Prop) t).
Proof. exact (eq_refl (@eq (_101211 -> Prop) t)). Qed.
Lemma lem3931287 {_101211 _101227 : Type'} (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (t = (t' x)) = (t = (@I (_101227 -> _101211 -> Prop) t' x)).
Proof. exact (MK_COMB (@lem3931286 _101211 t) (@lem3931285 _101211 _101227 t' x)). Qed.
Lemma lem3931288 {_101211 _101227 : Type'} (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term660 _101211 _101227 t t' x) = (term901 _101211 _101227 t t' x).
Proof. exact (MK_COMB (@lem3931275) (@lem3931287 _101211 _101227 t t' x)). Qed.
Lemma lem3931289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931295 {_101227 : Type'} (f : _101227 -> Prop) (x : _101227) : (f x) = (@I (_101227 -> Prop) f x).
Proof. exact (@lem3931294 _101227 Prop f x). Qed.
Lemma lem3931297 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (s x) = (@I (_101227 -> Prop) s x).
Proof. exact (@lem3931295 _101227 s x). Qed.
Lemma lem3931298 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (term474 _101227 s x) = (term900 _101227 s x).
Proof. exact (MK_COMB (@lem3931289) (@lem3931297 _101227 s x)). Qed.
Lemma lem3931299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931300 {_101227 : Type'} (s : _101227 -> Prop) (x : _101227) : (term914 _101227 s x) = (term915 _101227 s x).
Proof. exact (MK_COMB (@lem3931299) (@lem3931298 _101227 s x)). Qed.
Lemma lem3931301 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term688 _101211 _101227 s t t' x) = (term916 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931300 _101227 s x) (@lem3931288 _101211 _101227 t t' x)). Qed.
Lemma lem3931302 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term694 _101211 _101227 s t t') = (term917 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3931301 _101211 _101227 s t t' x)). Qed.
Lemma lem3931303 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931304 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term695 _101211 _101227 s t t') = (term918 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3931303 _101227) (@lem3931302 _101211 _101227 s t t')). Qed.
Lemma lem3931305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931306 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term697 _101211 _101227 s t t') = (term919 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3931305) (@lem3931304 _101211 _101227 s t t')). Qed.
Lemma lem3931307 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term699 _101211 _101227 s t t' x) = (term920 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931306 _101211 _101227 s t' t) (@lem3931274 _101211 t' x)). Qed.
Lemma lem3931308 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term706 _101211 _101227 s t x) = (term921 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931307 _101211 _101227 s t t' x)). Qed.
Lemma lem3931309 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931310 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term707 _101211 _101227 s t x) = (term922 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3931309 _101211) (@lem3931308 _101211 _101227 s t x)). Qed.
Lemma lem3931311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3931318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931319 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931318 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931320 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : (t a) = (@I (_101227 -> _101211 -> Prop) t a).
Proof. exact (@lem3931319 _101211 _101227 t a). Qed.
Lemma lem3931321 {_101211 : Type'} (x : _101211) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3931322 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (t a x) = (@I (_101227 -> _101211 -> Prop) t a x).
Proof. exact (MK_COMB (@lem3931320 _101211 _101227 t a) (@lem3931321 _101211 x)). Qed.
Lemma lem3931324 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931325 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931324 _101211 Prop f x). Qed.
Lemma lem3931326 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (@I (_101227 -> _101211 -> Prop) t a x) = (term897 _101211 _101227 t a x).
Proof. exact (@lem3931325 _101211 (@I (_101227 -> _101211 -> Prop) t a) x). Qed.
Lemma lem3931328 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (t a x) = (term897 _101211 _101227 t a x).
Proof. exact (TRANS (@lem3931322 _101211 _101227 t a x) (@lem3931326 _101211 _101227 t a x)). Qed.
Lemma lem3931329 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term923 _101211 _101227 t a x) = (term924 _101211 _101227 t a x).
Proof. exact (MK_COMB (@lem3931311) (@lem3931328 _101211 _101227 t a x)). Qed.
Lemma lem3931330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931331 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term708 _101211 _101227 t a x) = (term925 _101211 _101227 t a x).
Proof. exact (MK_COMB (@lem3931330) (@lem3931329 _101211 _101227 t a x)). Qed.
Lemma lem3931332 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term710 _101211 _101227 a s t x) = (term926 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931331 _101211 _101227 t a x) (@lem3931310 _101211 _101227 s t x)). Qed.
Lemma lem3931337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931338 {_101211 : Type'} (f : _101211 -> Prop) (x : _101211) : (f x) = (@I (_101211 -> Prop) f x).
Proof. exact (@lem3931337 _101211 Prop f x). Qed.
Lemma lem3931340 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (t' x) = (@I (_101211 -> Prop) t' x).
Proof. exact (@lem3931338 _101211 t' x). Qed.
Lemma lem3931347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931348 {_101211 _101227 : Type'} (f : type1470 _101211 _101227) (x : _101227) : (f x) = (@I (_101227 -> _101211 -> Prop) f x).
Proof. exact (@lem3931347 _101227 (_101211 -> Prop) f x). Qed.
Lemma lem3931350 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (@lem3931348 _101211 _101227 t x'). Qed.
Lemma lem3931351 {_101211 : Type'} (t' : _101211 -> Prop) : (@eq (_101211 -> Prop) t') = (@eq (_101211 -> Prop) t').
Proof. exact (eq_refl (@eq (_101211 -> Prop) t')). Qed.
Lemma lem3931352 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (t' = (t x')) = (t' = (@I (_101227 -> _101211 -> Prop) t x')).
Proof. exact (MK_COMB (@lem3931351 _101211 t') (@lem3931350 _101211 _101227 t x')). Qed.
Lemma lem3931357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3931358 {_101227 : Type'} (f : _101227 -> Prop) (x : _101227) : (f x) = (@I (_101227 -> Prop) f x).
Proof. exact (@lem3931357 _101227 Prop f x). Qed.
Lemma lem3931360 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) : (s x') = (@I (_101227 -> Prop) s x').
Proof. exact (@lem3931358 _101227 s x'). Qed.
Lemma lem3931367 {_101227 : Type'} (x' : _101227) (a : _101227) : (term557 _101227 x' a) = (term557 _101227 x' a).
Proof. exact (eq_refl (term557 _101227 x' a)). Qed.
Lemma lem3931368 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x' : _101227) : (term558 _101227 a s x') = (term927 _101227 a s x').
Proof. exact (MK_COMB (@lem3931367 _101227 x' a) (@lem3931360 _101227 s x')). Qed.
Lemma lem3931369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931370 {_101227 : Type'} (a : _101227) (s : _101227 -> Prop) (x' : _101227) : (term560 _101227 a s x') = (term928 _101227 a s x').
Proof. exact (MK_COMB (@lem3931369) (@lem3931368 _101227 a s x')). Qed.
Lemma lem3931371 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term572 _101211 _101227 a s t' t x') = (term929 _101211 _101227 a s t' t x').
Proof. exact (MK_COMB (@lem3931370 _101227 a s x') (@lem3931352 _101211 _101227 t' t x')). Qed.
Lemma lem3931372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931373 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term731 _101211 _101227 a s t' t x') = (term930 _101211 _101227 a s t' t x').
Proof. exact (MK_COMB (@lem3931372) (@lem3931371 _101211 _101227 a s t' t x')). Qed.
Lemma lem3931374 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term733 _101211 _101227 a s t x' t' x) = (term931 _101211 _101227 a s t x' t' x).
Proof. exact (MK_COMB (@lem3931373 _101211 _101227 a s t' t x') (@lem3931340 _101211 t' x)). Qed.
Lemma lem3931375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3931376 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term767 _101211 _101227 a s t x' t' x) = (term932 _101211 _101227 a s t x' t' x).
Proof. exact (MK_COMB (@lem3931375) (@lem3931374 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931377 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term769 _101211 _101227 x' t' a s t x) = (term933 _101211 _101227 x' t' a s t x).
Proof. exact (MK_COMB (@lem3931376 _101211 _101227 a s t x' t' x) (@lem3931332 _101211 _101227 a s t x)). Qed.
Lemma lem3931378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931379 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term885 _101211 _101227 x' t' a s t x) = (term934 _101211 _101227 x' t' a s t x).
Proof. exact (MK_COMB (@lem3931378) (@lem3931377 _101211 _101227 x' t' a s t x)). Qed.
Lemma lem3931380 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) : (term887 _101211 _101227 a s t x' t' x) = (term935 _101211 _101227 a s t x' t' x).
Proof. exact (MK_COMB (@lem3931379 _101211 _101227 x' t' a s t x) (@lem3931264 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931381 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term887 _101211 _101227 a s t x' t' x) : term935 _101211 _101227 a s t x' t' x.
Proof. exact (EQ_MP (@lem3931380 _101211 _101227 a s t x' t' x) (@lem3931151 _101211 _101227 a s t x' t' x h1)). Qed.
Lemma lem3931382 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term933 _101211 _101227 x' t' a s t x.
Proof. exact (h1). Qed.
Lemma lem3931383 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term913 _101211 _101227 a s t x' t' x.
Proof. exact (h1). Qed.
Lemma lem3931384 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term926 _101211 _101227 a s t x.
Proof. exact (proj2 (@lem3931382 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931385 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term931 _101211 _101227 a s t x' t' x.
Proof. exact (proj1 (@lem3931382 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931386 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term922 _101211 _101227 s t x.
Proof. exact (proj2 (@lem3931384 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931389 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term929 _101211 _101227 a s t' t x'.
Proof. exact (proj1 (@lem3931385 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931391 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term927 _101227 a s x'.
Proof. exact (proj1 (@lem3931389 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931394 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term899 _101211 _101227 a s t x' t' x.
Proof. exact (proj2 (@lem3931383 _101211 _101227 a s t x' t' x h1)). Qed.
Lemma lem3931395 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term911 _101211 _101227 a s t x.
Proof. exact (proj1 (@lem3931383 _101211 _101227 a s t x' t' x h1)). Qed.
Lemma lem3931397 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term896 _101211 _101227 s t x' t' x.
Proof. exact (h1). Qed.
Lemma lem3931399 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term894 _101211 _101227 s t' t x'.
Proof. exact (proj1 (@lem3931397 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3931465 {_101227 : Type'} (x' : _101227) (a : _101227) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3931471 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term937 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3931472 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term936 _101227 P Q) = (term937 _101227 P Q).
Proof. exact (@lem3931471 _101227 P Q). Qed.
Lemma lem3931473 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term938 _101211 _101227 s t t' x) = (term939 _101211 _101227 s t t' x).
Proof. exact (@lem3931472 _101227 (term917 _101211 _101227 s t' t) (term900 _101211 t' x)). Qed.
Lemma lem3931474 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term940 _101211 _101227 s t t' x) = (term916 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term940 _101211 _101227 s t t' x)). Qed.
Lemma lem3931475 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term941 _101211 _101227 s t t') = (term917 _101211 _101227 s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3931474 _101211 _101227 s t t' x)). Qed.
Lemma lem3931476 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931477 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term942 _101211 _101227 s t t') = (term918 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3931476 _101227) (@lem3931475 _101211 _101227 s t t')). Qed.
Lemma lem3931478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931479 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term943 _101211 _101227 s t t') = (term919 _101211 _101227 s t t').
Proof. exact (MK_COMB (@lem3931478) (@lem3931477 _101211 _101227 s t t')). Qed.
Lemma lem3931480 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931481 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term938 _101211 _101227 s t t' x) = (term920 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931479 _101211 _101227 s t' t) (@lem3931480 _101211 t' x)). Qed.
Lemma lem3931482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931483 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term944 _101211 _101227 s t t' x) = (term945 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931482) (@lem3931481 _101211 _101227 s t t' x)). Qed.
Lemma lem3931484 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term940 _101211 _101227 s t t' x) = (term916 _101211 _101227 s t t' x).
Proof. exact (eq_refl (term940 _101211 _101227 s t t' x)). Qed.
Lemma lem3931485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931486 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term946 _101211 _101227 s t t' x) = (term947 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931485) (@lem3931484 _101211 _101227 s t t' x)). Qed.
Lemma lem3931487 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931488 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term948 _101211 _101227 s t x t' x') = (term949 _101211 _101227 s t x t' x').
Proof. exact (MK_COMB (@lem3931486 _101211 _101227 s t' t x) (@lem3931487 _101211 t' x')). Qed.
Lemma lem3931489 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term950 _101211 _101227 s t t' x) = (term951 _101211 _101227 s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931488 _101211 _101227 s t x' t' x)). Qed.
Lemma lem3931490 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931491 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term939 _101211 _101227 s t t' x) = (term952 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931490 _101227) (@lem3931489 _101211 _101227 s t t' x)). Qed.
Lemma lem3931492 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term938 _101211 _101227 s t t' x) = (term939 _101211 _101227 s t t' x)) = ((term920 _101211 _101227 s t t' x) = (term952 _101211 _101227 s t t' x)).
Proof. exact (MK_COMB (@lem3931483 _101211 _101227 s t t' x) (@lem3931491 _101211 _101227 s t t' x)). Qed.
Lemma lem3931493 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term920 _101211 _101227 s t t' x) = (term952 _101211 _101227 s t t' x).
Proof. exact (EQ_MP (@lem3931492 _101211 _101227 s t t' x) (@lem3931473 _101211 _101227 s t t' x)). Qed.
Lemma lem3931494 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term921 _101211 _101227 s t x) = (term953 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931493 _101211 _101227 s t t' x)). Qed.
Lemma lem3931495 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931496 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term922 _101211 _101227 s t x) = (term954 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3931495 _101211) (@lem3931494 _101211 _101227 s t x)). Qed.
Lemma lem3931509 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term949 _101211 _101227 s t x t' x') = (term949 _101211 _101227 s t x t' x').
Proof. exact (eq_refl (term949 _101211 _101227 s t x t' x')). Qed.
Lemma lem3931510 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term951 _101211 _101227 s t t' x) = (term951 _101211 _101227 s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931509 _101211 _101227 s t x' t' x)). Qed.
Lemma lem3931511 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931512 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term952 _101211 _101227 s t t' x) = (term952 _101211 _101227 s t t' x).
Proof. exact (MK_COMB (@lem3931511 _101227) (@lem3931510 _101211 _101227 s t t' x)). Qed.
Lemma lem3931513 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term953 _101211 _101227 s t x) = (term953 _101211 _101227 s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931512 _101211 _101227 s t t' x)). Qed.
Lemma lem3931514 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931515 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term954 _101211 _101227 s t x) = (term954 _101211 _101227 s t x).
Proof. exact (MK_COMB (@lem3931514 _101211) (@lem3931513 _101211 _101227 s t x)). Qed.
Lemma lem3931516 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term922 _101211 _101227 s t x) = (term954 _101211 _101227 s t x).
Proof. exact (TRANS (@lem3931496 _101211 _101227 s t x) (@lem3931515 _101211 _101227 s t x)). Qed.
Lemma lem3931517 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term954 _101211 _101227 s t x.
Proof. exact (EQ_MP (@lem3931516 _101211 _101227 s t x) (@lem3931386 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931529 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : @I (_101227 -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3931531 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term937 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3931532 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term936 _101227 P Q) = (term937 _101227 P Q).
Proof. exact (@lem3931531 _101227 P Q). Qed.
Lemma lem3931533 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term955 _101211 _101227 a s t t' x) = (term956 _101211 _101227 a s t t' x).
Proof. exact (@lem3931532 _101227 (term906 _101211 _101227 a s t' t) (term900 _101211 t' x)). Qed.
Lemma lem3931534 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term957 _101211 _101227 a s t t' x) = (term905 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term957 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931535 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term958 _101211 _101227 a s t t') = (term906 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3931534 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931536 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931537 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term959 _101211 _101227 a s t t') = (term907 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931536 _101227) (@lem3931535 _101211 _101227 a s t t')). Qed.
Lemma lem3931538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931539 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term960 _101211 _101227 a s t t') = (term908 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931538) (@lem3931537 _101211 _101227 a s t t')). Qed.
Lemma lem3931540 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931541 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term955 _101211 _101227 a s t t' x) = (term909 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931539 _101211 _101227 a s t' t) (@lem3931540 _101211 t' x)). Qed.
Lemma lem3931542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931543 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term961 _101211 _101227 a s t t' x) = (term962 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931542) (@lem3931541 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931544 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term957 _101211 _101227 a s t t' x) = (term905 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term957 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931546 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term963 _101211 _101227 a s t t' x) = (term964 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931545) (@lem3931544 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931547 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931548 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term965 _101211 _101227 a s t x t' x') = (term966 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931546 _101211 _101227 a s t' t x) (@lem3931547 _101211 t' x')). Qed.
Lemma lem3931549 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term967 _101211 _101227 a s t t' x) = (term968 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931548 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931550 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931551 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term956 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931550 _101227) (@lem3931549 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931552 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term955 _101211 _101227 a s t t' x) = (term956 _101211 _101227 a s t t' x)) = ((term909 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3931543 _101211 _101227 a s t t' x) (@lem3931551 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931553 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term909 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3931552 _101211 _101227 a s t t' x) (@lem3931533 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931554 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term910 _101211 _101227 a s t x) = (term970 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931553 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931555 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931556 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term911 _101211 _101227 a s t x) = (term971 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931555 _101211) (@lem3931554 _101211 _101227 a s t x)). Qed.
Lemma lem3931557 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931574 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term905 _101211 _101227 a s t t' x) = (term972 _101211 _101227 a s t t' x).
Proof. exact (@lem19699 (term973 _101227 x a) (term900 _101227 s x) (term901 _101211 _101227 t t' x)). Qed.
Lemma lem3931575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931576 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term964 _101211 _101227 a s t t' x) = (term974 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931575) (@lem3931574 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931577 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term966 _101211 _101227 a s t x t' x') = (term975 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931576 _101211 _101227 a s t' t x) (@lem3931557 _101211 t' x')). Qed.
Lemma lem3931584 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term975 _101211 _101227 a s t x t' x') = (term976 _101211 _101227 a s t x t' x').
Proof. exact (@lem19699 (term977 _101211 _101227 a t' t x) (term916 _101211 _101227 s t' t x) (term900 _101211 t' x')). Qed.
Lemma lem3931585 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term966 _101211 _101227 a s t x t' x') = (term976 _101211 _101227 a s t x t' x').
Proof. exact (TRANS (@lem3931577 _101211 _101227 a s t x t' x') (@lem3931584 _101211 _101227 a s t x t' x')). Qed.
Lemma lem3931586 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term968 _101211 _101227 a s t t' x) = (term978 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931585 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931587 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931588 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term969 _101211 _101227 a s t t' x) = (term979 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931587 _101227) (@lem3931586 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931589 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term970 _101211 _101227 a s t x) = (term980 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931588 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931590 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931591 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term971 _101211 _101227 a s t x) = (term981 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931590 _101211) (@lem3931589 _101211 _101227 a s t x)). Qed.
Lemma lem3931592 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term911 _101211 _101227 a s t x) = (term981 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931556 _101211 _101227 a s t x) (@lem3931591 _101211 _101227 a s t x)). Qed.
Lemma lem3931593 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term981 _101211 _101227 a s t x.
Proof. exact (EQ_MP (@lem3931592 _101211 _101227 a s t x) (@lem3931395 _101211 _101227 a s t x' t' x h1)). Qed.
Lemma lem3931597 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term897 _101211 _101227 t a x.
Proof. exact (h1). Qed.
Lemma lem3931599 {A : Type'} (P : A -> Prop) (Q : Prop) : (term936 A P Q) = (term937 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3931600 {_101227 : Type'} (P : _101227 -> Prop) (Q : Prop) : (term936 _101227 P Q) = (term937 _101227 P Q).
Proof. exact (@lem3931599 _101227 P Q). Qed.
Lemma lem3931601 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term955 _101211 _101227 a s t t' x) = (term956 _101211 _101227 a s t t' x).
Proof. exact (@lem3931600 _101227 (term906 _101211 _101227 a s t' t) (term900 _101211 t' x)). Qed.
Lemma lem3931602 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term957 _101211 _101227 a s t t' x) = (term905 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term957 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931603 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term958 _101211 _101227 a s t t') = (term906 _101211 _101227 a s t t').
Proof. exact (fun_ext (fun x : _101227 => @lem3931602 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931604 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931605 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term959 _101211 _101227 a s t t') = (term907 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931604 _101227) (@lem3931603 _101211 _101227 a s t t')). Qed.
Lemma lem3931606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931607 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) : (term960 _101211 _101227 a s t t') = (term908 _101211 _101227 a s t t').
Proof. exact (MK_COMB (@lem3931606) (@lem3931605 _101211 _101227 a s t t')). Qed.
Lemma lem3931608 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931609 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term955 _101211 _101227 a s t t' x) = (term909 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931607 _101211 _101227 a s t' t) (@lem3931608 _101211 t' x)). Qed.
Lemma lem3931610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931611 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term961 _101211 _101227 a s t t' x) = (term962 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931610) (@lem3931609 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931612 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term957 _101211 _101227 a s t t' x) = (term905 _101211 _101227 a s t t' x).
Proof. exact (eq_refl (term957 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931614 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term963 _101211 _101227 a s t t' x) = (term964 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931613) (@lem3931612 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931615 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931616 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term965 _101211 _101227 a s t x t' x') = (term966 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931614 _101211 _101227 a s t' t x) (@lem3931615 _101211 t' x')). Qed.
Lemma lem3931617 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term967 _101211 _101227 a s t t' x) = (term968 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931616 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931618 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931619 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term956 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931618 _101227) (@lem3931617 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931620 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : ((term955 _101211 _101227 a s t t' x) = (term956 _101211 _101227 a s t t' x)) = ((term909 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x)).
Proof. exact (MK_COMB (@lem3931611 _101211 _101227 a s t t' x) (@lem3931619 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931621 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term909 _101211 _101227 a s t t' x) = (term969 _101211 _101227 a s t t' x).
Proof. exact (EQ_MP (@lem3931620 _101211 _101227 a s t t' x) (@lem3931601 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931622 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term910 _101211 _101227 a s t x) = (term970 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931621 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931623 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931624 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term911 _101211 _101227 a s t x) = (term971 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931623 _101211) (@lem3931622 _101211 _101227 a s t x)). Qed.
Lemma lem3931625 {_101211 : Type'} (t : _101211 -> Prop) (x : _101211) : (term900 _101211 t x) = (term900 _101211 t x).
Proof. exact (eq_refl (term900 _101211 t x)). Qed.
Lemma lem3931642 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term905 _101211 _101227 a s t t' x) = (term972 _101211 _101227 a s t t' x).
Proof. exact (@lem19699 (term973 _101227 x a) (term900 _101227 s x) (term901 _101211 _101227 t t' x)). Qed.
Lemma lem3931643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3931644 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : _101211 -> Prop) (t' : type1470 _101211 _101227) (x : _101227) : (term964 _101211 _101227 a s t t' x) = (term974 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931643) (@lem3931642 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931645 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term966 _101211 _101227 a s t x t' x') = (term975 _101211 _101227 a s t x t' x').
Proof. exact (MK_COMB (@lem3931644 _101211 _101227 a s t' t x) (@lem3931625 _101211 t' x')). Qed.
Lemma lem3931652 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term975 _101211 _101227 a s t x t' x') = (term976 _101211 _101227 a s t x t' x').
Proof. exact (@lem19699 (term977 _101211 _101227 a t' t x) (term916 _101211 _101227 s t' t x) (term900 _101211 t' x')). Qed.
Lemma lem3931653 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101227) (t' : _101211 -> Prop) (x' : _101211) : (term966 _101211 _101227 a s t x t' x') = (term976 _101211 _101227 a s t x t' x').
Proof. exact (TRANS (@lem3931645 _101211 _101227 a s t x t' x') (@lem3931652 _101211 _101227 a s t x t' x')). Qed.
Lemma lem3931654 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term968 _101211 _101227 a s t t' x) = (term978 _101211 _101227 a s t t' x).
Proof. exact (fun_ext (fun x' : _101227 => @lem3931653 _101211 _101227 a s t x' t' x)). Qed.
Lemma lem3931655 {_101227 : Type'} : (@all _101227) = (@all _101227).
Proof. exact (eq_refl (@all _101227)). Qed.
Lemma lem3931656 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) : (term969 _101211 _101227 a s t t' x) = (term979 _101211 _101227 a s t t' x).
Proof. exact (MK_COMB (@lem3931655 _101227) (@lem3931654 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931657 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term970 _101211 _101227 a s t x) = (term980 _101211 _101227 a s t x).
Proof. exact (fun_ext (fun t' : _101211 -> Prop => @lem3931656 _101211 _101227 a s t t' x)). Qed.
Lemma lem3931658 {_101211 : Type'} : (@all (_101211 -> Prop)) = (@all (_101211 -> Prop)).
Proof. exact (eq_refl (@all (_101211 -> Prop))). Qed.
Lemma lem3931659 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term971 _101211 _101227 a s t x) = (term981 _101211 _101227 a s t x).
Proof. exact (MK_COMB (@lem3931658 _101211) (@lem3931657 _101211 _101227 a s t x)). Qed.
Lemma lem3931660 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term911 _101211 _101227 a s t x) = (term981 _101211 _101227 a s t x).
Proof. exact (TRANS (@lem3931624 _101211 _101227 a s t x) (@lem3931659 _101211 _101227 a s t x)). Qed.
Lemma lem3931661 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term981 _101211 _101227 a s t x.
Proof. exact (EQ_MP (@lem3931660 _101211 _101227 a s t x) (@lem3931395 _101211 _101227 a s t x' t' x h1)). Qed.
Lemma lem3931680 {_101211 _101227 : Type'} (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term982 _101211 _101227 s t x _45668.
Proof. exact (@lem3931517 _101211 _101227 x' t' a s t x h1 _45668). Qed.
Lemma lem3931681 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term982 _101211 _101227 s t x _45668) = (term952 _101211 _101227 s t _45668 x).
Proof. exact (eq_refl (term982 _101211 _101227 s t x _45668)). Qed.
Lemma lem3931682 {_101211 _101227 : Type'} (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term952 _101211 _101227 s t _45668 x.
Proof. exact (EQ_MP (@lem3931681 _101211 _101227 s t _45668 x) (@lem3931680 _101211 _101227 _45668 x' t' a s t x h1)). Qed.
Lemma lem3931683 {_101211 _101227 : Type'} (_45668 : _101211 -> Prop) (_45669 : _101227) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term983 _101211 _101227 s t _45668 x _45669.
Proof. exact (@lem3931682 _101211 _101227 _45668 x' t' a s t x h1 _45669). Qed.
Lemma lem3931684 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term983 _101211 _101227 s t _45668 x _45669) = (term949 _101211 _101227 s t _45669 _45668 x).
Proof. exact (eq_refl (term983 _101211 _101227 s t _45668 x _45669)). Qed.
Lemma lem3931685 {_101211 _101227 : Type'} (_45669 : _101227) (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term949 _101211 _101227 s t _45669 _45668 x.
Proof. exact (EQ_MP (@lem3931684 _101211 _101227 s t _45669 _45668 x) (@lem3931683 _101211 _101227 _45668 _45669 x' t' a s t x h1)). Qed.
Lemma lem3931686 {_101211 _101227 : Type'} (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term984 _101211 _101227 a s t x _45670.
Proof. exact (@lem3931593 _101211 _101227 a s t x' t' x h1 _45670). Qed.
Lemma lem3931687 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term984 _101211 _101227 a s t x _45670) = (term979 _101211 _101227 a s t _45670 x).
Proof. exact (eq_refl (term984 _101211 _101227 a s t x _45670)). Qed.
Lemma lem3931688 {_101211 _101227 : Type'} (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term979 _101211 _101227 a s t _45670 x.
Proof. exact (EQ_MP (@lem3931687 _101211 _101227 a s t _45670 x) (@lem3931686 _101211 _101227 _45670 a s t x' t' x h1)). Qed.
Lemma lem3931689 {_101211 _101227 : Type'} (_45670 : _101211 -> Prop) (_45671 : _101227) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term985 _101211 _101227 a s t _45670 x _45671.
Proof. exact (@lem3931688 _101211 _101227 _45670 a s t x' t' x h1 _45671). Qed.
Lemma lem3931690 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term985 _101211 _101227 a s t _45670 x _45671) = (term976 _101211 _101227 a s t _45671 _45670 x).
Proof. exact (eq_refl (term985 _101211 _101227 a s t _45670 x _45671)). Qed.
Lemma lem3931691 {_101211 _101227 : Type'} (_45671 : _101227) (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term976 _101211 _101227 a s t _45671 _45670 x.
Proof. exact (EQ_MP (@lem3931690 _101211 _101227 a s t _45671 _45670 x) (@lem3931689 _101211 _101227 _45670 _45671 a s t x' t' x h1)). Qed.
Lemma lem3931692 {_101211 _101227 : Type'} (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term984 _101211 _101227 a s t x _45672.
Proof. exact (@lem3931661 _101211 _101227 a s t x' t' x h1 _45672). Qed.
Lemma lem3931693 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term984 _101211 _101227 a s t x _45672) = (term979 _101211 _101227 a s t _45672 x).
Proof. exact (eq_refl (term984 _101211 _101227 a s t x _45672)). Qed.
Lemma lem3931694 {_101211 _101227 : Type'} (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term979 _101211 _101227 a s t _45672 x.
Proof. exact (EQ_MP (@lem3931693 _101211 _101227 a s t _45672 x) (@lem3931692 _101211 _101227 _45672 a s t x' t' x h1)). Qed.
Lemma lem3931695 {_101211 _101227 : Type'} (_45672 : _101211 -> Prop) (_45673 : _101227) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term985 _101211 _101227 a s t _45672 x _45673.
Proof. exact (@lem3931694 _101211 _101227 _45672 a s t x' t' x h1 _45673). Qed.
Lemma lem3931696 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term985 _101211 _101227 a s t _45672 x _45673) = (term976 _101211 _101227 a s t _45673 _45672 x).
Proof. exact (eq_refl (term985 _101211 _101227 a s t _45672 x _45673)). Qed.
Lemma lem3931697 {_101211 _101227 : Type'} (_45673 : _101227) (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term976 _101211 _101227 a s t _45673 _45672 x.
Proof. exact (EQ_MP (@lem3931696 _101211 _101227 a s t _45673 _45672 x) (@lem3931695 _101211 _101227 _45672 _45673 a s t x' t' x h1)). Qed.
Lemma lem3931699 {_101211 _101227 : Type'} (_45671 : _101227) (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term986 _101211 _101227 a t _45671 _45670 x.
Proof. exact (proj1 (@lem3931691 _101211 _101227 _45671 _45670 a s t x' t' x h1)). Qed.
Lemma lem3931700 {_101211 _101227 : Type'} (_45673 : _101227) (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term949 _101211 _101227 s t _45673 _45672 x.
Proof. exact (proj2 (@lem3931697 _101211 _101227 _45673 _45672 a s t x' t' x h1)). Qed.
Lemma lem3931719 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : t' = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (proj2 (@lem3931389 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931721 {_101227 : Type'} (x' : _101227) (a : _101227) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3931734 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term949 _101211 _101227 s t _45669 _45668 x) = (term987 _101211 _101227 s t _45669 _45668 x).
Proof. exact (@lem3929727 (term900 _101227 s _45669) (term901 _101211 _101227 _45668 t _45669) (term900 _101211 _45668 x)). Qed.
Lemma lem3931737 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : @I (_101211 -> Prop) t' x.
Proof. exact (proj2 (@lem3931385 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931739 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : t' = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (proj2 (@lem3931389 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931741 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : @I (_101227 -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3931743 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term897 _101211 _101227 t a x.
Proof. exact (h1). Qed.
Lemma lem3931754 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term986 _101211 _101227 a t _45671 _45670 x) = (term988 _101211 _101227 a t _45671 _45670 x).
Proof. exact (@lem3929727 (term973 _101227 _45671 a) (term901 _101211 _101227 _45670 t _45671) (term900 _101211 _45670 x)). Qed.
Lemma lem3931755 {_101211 _101227 : Type'} (_45671 : _101227) (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term988 _101211 _101227 a t _45671 _45670 x.
Proof. exact (EQ_MP (@lem3931754 _101211 _101227 a t _45671 _45670 x) (@lem3931699 _101211 _101227 _45671 _45670 a s t x' t' x h1)). Qed.
Lemma lem3931769 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : @I (_101211 -> Prop) t' x.
Proof. exact (proj2 (@lem3931397 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3931773 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : t' = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (proj2 (@lem3931399 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3931796 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term949 _101211 _101227 s t _45673 _45672 x) = (term987 _101211 _101227 s t _45673 _45672 x).
Proof. exact (@lem3929727 (term900 _101227 s _45673) (term901 _101211 _101227 _45672 t _45673) (term900 _101211 _45672 x)). Qed.
Lemma lem3931853 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : @I (_101211 -> Prop) t' x.
Proof. exact (proj2 (@lem3931385 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931854 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) : (term989 _101211 _101227 t' t) = (term989 _101211 _101227 t' t).
Proof. exact (eq_refl (term989 _101211 _101227 t' t)). Qed.
Lemma lem3931855 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (a : _101227) (h1 : x' = a) : (term990 _101211 _101227 t' t x') = (term990 _101211 _101227 t' t a).
Proof. exact (MK_COMB (@lem3931854 _101211 _101227 t' t) (@lem3931721 _101227 x' a h1)). Qed.
Lemma lem3931856 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : (term990 _101211 _101227 t' t a) = (t' = (@I (_101227 -> _101211 -> Prop) t a)).
Proof. exact (eq_refl (term990 _101211 _101227 t' t a)). Qed.
Lemma lem3931857 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term991 _101211 _101227 t' t x') = (term991 _101211 _101227 t' t x').
Proof. exact (eq_refl (term991 _101211 _101227 t' t x')). Qed.
Lemma lem3931858 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : ((term990 _101211 _101227 t' t x') = (term990 _101211 _101227 t' t a)) = ((term990 _101211 _101227 t' t x') = (t' = (@I (_101227 -> _101211 -> Prop) t a))).
Proof. exact (MK_COMB (@lem3931857 _101211 _101227 t' t x') (@lem3931856 _101211 _101227 t' t a)). Qed.
Lemma lem3931859 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term990 _101211 _101227 t' t x') = (t' = (@I (_101227 -> _101211 -> Prop) t x')).
Proof. exact (eq_refl (term990 _101211 _101227 t' t x')). Qed.
Lemma lem3931860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931861 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) : (term991 _101211 _101227 t' t x') = (term992 _101211 _101227 t' t x').
Proof. exact (MK_COMB (@lem3931860) (@lem3931859 _101211 _101227 t' t x')). Qed.
Lemma lem3931862 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : (t' = (@I (_101227 -> _101211 -> Prop) t a)) = (t' = (@I (_101227 -> _101211 -> Prop) t a)).
Proof. exact (eq_refl (t' = (@I (_101227 -> _101211 -> Prop) t a))). Qed.
Lemma lem3931863 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : ((term990 _101211 _101227 t' t x') = (t' = (@I (_101227 -> _101211 -> Prop) t a))) = ((t' = (@I (_101227 -> _101211 -> Prop) t x')) = (t' = (@I (_101227 -> _101211 -> Prop) t a))).
Proof. exact (MK_COMB (@lem3931861 _101211 _101227 t' t x') (@lem3931862 _101211 _101227 t' t a)). Qed.
Lemma lem3931864 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : ((term990 _101211 _101227 t' t x') = (term990 _101211 _101227 t' t a)) = ((t' = (@I (_101227 -> _101211 -> Prop) t x')) = (t' = (@I (_101227 -> _101211 -> Prop) t a))).
Proof. exact (TRANS (@lem3931858 _101211 _101227 x' t' t a) (@lem3931863 _101211 _101227 x' t' t a)). Qed.
Lemma lem3931865 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (a : _101227) (h1 : x' = a) : (t' = (@I (_101227 -> _101211 -> Prop) t x')) = (t' = (@I (_101227 -> _101211 -> Prop) t a)).
Proof. exact (EQ_MP (@lem3931864 _101211 _101227 x' t' t a) (@lem3931855 _101211 _101227 t' t x' a h1)). Qed.
Lemma lem3931866 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : t' = (@I (_101227 -> _101211 -> Prop) t a).
Proof. exact (EQ_MP (@lem3931865 _101211 _101227 t' t x' a h2) (@lem3931719 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931894 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term924 _101211 _101227 t a x.
Proof. exact (proj1 (@lem3931384 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931909 {_101211 : Type'} (x : _101211) : (term993 _101211 x) = (term993 _101211 x).
Proof. exact (eq_refl (term993 _101211 x)). Qed.
Lemma lem3931910 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : (term994 _101211 x t') = (term995 _101211 _101227 x t a).
Proof. exact (MK_COMB (@lem3931909 _101211 x) (@lem3931866 _101211 _101227 t' s t x x' a h1 h2)). Qed.
Lemma lem3931911 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term995 _101211 _101227 x t a) = (term897 _101211 _101227 t a x).
Proof. exact (eq_refl (term995 _101211 _101227 x t a)). Qed.
Lemma lem3931912 {_101211 : Type'} (x : _101211) (t' : _101211 -> Prop) : (term996 _101211 x t') = (term996 _101211 x t').
Proof. exact (eq_refl (term996 _101211 x t')). Qed.
Lemma lem3931913 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t a)) = ((term994 _101211 x t') = (term897 _101211 _101227 t a x)).
Proof. exact (MK_COMB (@lem3931912 _101211 x t') (@lem3931911 _101211 _101227 t a x)). Qed.
Lemma lem3931914 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term994 _101211 x t') = (@I (_101211 -> Prop) t' x).
Proof. exact (eq_refl (term994 _101211 x t')). Qed.
Lemma lem3931915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931916 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term996 _101211 x t') = (term997 _101211 t' x).
Proof. exact (MK_COMB (@lem3931915) (@lem3931914 _101211 t' x)). Qed.
Lemma lem3931917 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term897 _101211 _101227 t a x) = (term897 _101211 _101227 t a x).
Proof. exact (eq_refl (term897 _101211 _101227 t a x)). Qed.
Lemma lem3931918 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : ((term994 _101211 x t') = (term897 _101211 _101227 t a x)) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t a x)).
Proof. exact (MK_COMB (@lem3931916 _101211 t' x) (@lem3931917 _101211 _101227 t a x)). Qed.
Lemma lem3931919 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t a)) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t a x)).
Proof. exact (TRANS (@lem3931913 _101211 _101227 t' t a x) (@lem3931918 _101211 _101227 t' t a x)). Qed.
Lemma lem3931920 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : (@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t a x).
Proof. exact (EQ_MP (@lem3931919 _101211 _101227 t' t a x) (@lem3931910 _101211 _101227 t' s t x x' a h1 h2)). Qed.
Lemma lem3931963 {_101211 _101227 : Type'} (_45669 : _101227) (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term987 _101211 _101227 s t _45669 _45668 x.
Proof. exact (EQ_MP (@lem3931734 _101211 _101227 s t _45669 _45668 x) (@lem3931685 _101211 _101227 _45669 _45668 x' t' a s t x h1)). Qed.
Lemma lem3931964 {_101211 : Type'} (x : _101211) : (term993 _101211 x) = (term993 _101211 x).
Proof. exact (eq_refl (term993 _101211 x)). Qed.
Lemma lem3931965 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : (term994 _101211 x t') = (term995 _101211 _101227 x t x').
Proof. exact (MK_COMB (@lem3931964 _101211 x) (@lem3931739 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931966 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term995 _101211 _101227 x t x') = (term897 _101211 _101227 t x' x).
Proof. exact (eq_refl (term995 _101211 _101227 x t x')). Qed.
Lemma lem3931967 {_101211 : Type'} (x : _101211) (t' : _101211 -> Prop) : (term996 _101211 x t') = (term996 _101211 x t').
Proof. exact (eq_refl (term996 _101211 x t')). Qed.
Lemma lem3931968 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t x')) = ((term994 _101211 x t') = (term897 _101211 _101227 t x' x)).
Proof. exact (MK_COMB (@lem3931967 _101211 x t') (@lem3931966 _101211 _101227 t x' x)). Qed.
Lemma lem3931969 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term994 _101211 x t') = (@I (_101211 -> Prop) t' x).
Proof. exact (eq_refl (term994 _101211 x t')). Qed.
Lemma lem3931970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3931971 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term996 _101211 x t') = (term997 _101211 t' x).
Proof. exact (MK_COMB (@lem3931970) (@lem3931969 _101211 t' x)). Qed.
Lemma lem3931972 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term897 _101211 _101227 t x' x) = (term897 _101211 _101227 t x' x).
Proof. exact (eq_refl (term897 _101211 _101227 t x' x)). Qed.
Lemma lem3931973 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term897 _101211 _101227 t x' x)) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x)).
Proof. exact (MK_COMB (@lem3931971 _101211 t' x) (@lem3931972 _101211 _101227 t x' x)). Qed.
Lemma lem3931974 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t x')) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x)).
Proof. exact (TRANS (@lem3931968 _101211 _101227 t' t x' x) (@lem3931973 _101211 _101227 t' t x' x)). Qed.
Lemma lem3931975 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : (@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x).
Proof. exact (EQ_MP (@lem3931974 _101211 _101227 t' t x' x) (@lem3931965 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3931990 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : @I (_101227 -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3932005 {_101211 : Type'} (x : _101211) : (term993 _101211 x) = (term993 _101211 x).
Proof. exact (eq_refl (term993 _101211 x)). Qed.
Lemma lem3932006 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : (term994 _101211 x t') = (term995 _101211 _101227 x t x').
Proof. exact (MK_COMB (@lem3932005 _101211 x) (@lem3931773 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932007 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term995 _101211 _101227 x t x') = (term897 _101211 _101227 t x' x).
Proof. exact (eq_refl (term995 _101211 _101227 x t x')). Qed.
Lemma lem3932008 {_101211 : Type'} (x : _101211) (t' : _101211 -> Prop) : (term996 _101211 x t') = (term996 _101211 x t').
Proof. exact (eq_refl (term996 _101211 x t')). Qed.
Lemma lem3932009 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t x')) = ((term994 _101211 x t') = (term897 _101211 _101227 t x' x)).
Proof. exact (MK_COMB (@lem3932008 _101211 x t') (@lem3932007 _101211 _101227 t x' x)). Qed.
Lemma lem3932010 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term994 _101211 x t') = (@I (_101211 -> Prop) t' x).
Proof. exact (eq_refl (term994 _101211 x t')). Qed.
Lemma lem3932011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3932012 {_101211 : Type'} (t' : _101211 -> Prop) (x : _101211) : (term996 _101211 x t') = (term997 _101211 t' x).
Proof. exact (MK_COMB (@lem3932011) (@lem3932010 _101211 t' x)). Qed.
Lemma lem3932013 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term897 _101211 _101227 t x' x) = (term897 _101211 _101227 t x' x).
Proof. exact (eq_refl (term897 _101211 _101227 t x' x)). Qed.
Lemma lem3932014 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term897 _101211 _101227 t x' x)) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x)).
Proof. exact (MK_COMB (@lem3932012 _101211 t' x) (@lem3932013 _101211 _101227 t x' x)). Qed.
Lemma lem3932015 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : ((term994 _101211 x t') = (term995 _101211 _101227 x t x')) = ((@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x)).
Proof. exact (TRANS (@lem3932009 _101211 _101227 t' t x' x) (@lem3932014 _101211 _101227 t' t x' x)). Qed.
Lemma lem3932016 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : (@I (_101211 -> Prop) t' x) = (term897 _101211 _101227 t x' x).
Proof. exact (EQ_MP (@lem3932015 _101211 _101227 t' t x' x) (@lem3932006 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932059 {_101211 _101227 : Type'} (_45673 : _101227) (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term987 _101211 _101227 s t _45673 _45672 x.
Proof. exact (EQ_MP (@lem3931796 _101211 _101227 s t _45673 _45672 x) (@lem3931700 _101211 _101227 _45673 _45672 a s t x' t' x h1)). Qed.
Lemma lem3932124 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : term897 _101211 _101227 t a x.
Proof. exact (EQ_MP (@lem3931920 _101211 _101227 t' s t x x' a h1 h2) (@lem3931853 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932125 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : term998 _101211 _101227 t a x.
Proof. exact (fun h0 : term924 _101211 _101227 t a x => @lem3932124 _101211 _101227 t' s t x x' a h1 h2). Qed.
Lemma lem3932127 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932128 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term998 _101211 _101227 t a x) = (term897 _101211 _101227 t a x).
Proof. exact (@lem3932127 (term897 _101211 _101227 t a x)). Qed.
Lemma lem3932129 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : term897 _101211 _101227 t a x.
Proof. exact (EQ_MP (@lem3932128 _101211 _101227 t a x) (@lem3932125 _101211 _101227 t' s t x x' a h1 h2)). Qed.
Lemma lem3932132 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3932134 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term924 _101211 _101227 t a x) = (term999 _101211 _101227 t a x).
Proof. exact (@lem3932132 (term897 _101211 _101227 t a x)). Qed.
Lemma lem3932137 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term999 _101211 _101227 t a x.
Proof. exact (EQ_MP (@lem3932134 _101211 _101227 t a x) (@lem3931894 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932140 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : False.
Proof. exact (@lem3932137 _101211 _101227 x' t' a s t x h1 (@lem3932129 _101211 _101227 t' s t x x' a h1 h2)). Qed.
Lemma lem3932141 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : term482.
Proof. exact (fun h0 : ~ False => @lem3932140 _101211 _101227 t' s t x x' a h1 h2). Qed.
Lemma lem3932143 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932144 : term482 = False.
Proof. exact (@lem3932143 False). Qed.
Lemma lem3932210 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : @I (_101227 -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3932211 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : term1000 _101227 s x'.
Proof. exact (fun h0 : term900 _101227 s x' => @lem3932210 _101227 s x' h1). Qed.
Lemma lem3932213 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932214 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) : (term1000 _101227 s x') = (@I (_101227 -> Prop) s x').
Proof. exact (@lem3932213 (@I (_101227 -> Prop) s x')). Qed.
Lemma lem3932215 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (h1 : @I (_101227 -> Prop) s x') : @I (_101227 -> Prop) s x'.
Proof. exact (EQ_MP (@lem3932214 _101227 s x') (@lem3932211 _101227 s x' h1)). Qed.
Lemma lem3932217 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem21386 (_101211 -> Prop) x). Qed.
Lemma lem3932218 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem3932217 _101211 x). Qed.
Lemma lem3932219 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (@lem3932218 _101211 (@I (_101227 -> _101211 -> Prop) t x')). Qed.
Lemma lem3932220 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : term1001 _101211 _101227 t x'.
Proof. exact (fun h0 : term1002 _101211 _101227 t x' => @lem3932219 _101211 _101227 t x'). Qed.
Lemma lem3932222 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932223 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (term1001 _101211 _101227 t x') = ((@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x')).
Proof. exact (@lem3932222 ((@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x'))). Qed.
Lemma lem3932224 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (EQ_MP (@lem3932223 _101211 _101227 t x') (@lem3932220 _101211 _101227 t x')). Qed.
Lemma lem3932226 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term897 _101211 _101227 t x' x.
Proof. exact (EQ_MP (@lem3931975 _101211 _101227 x' t' a s t x h1) (@lem3931737 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932227 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term998 _101211 _101227 t x' x.
Proof. exact (fun h0 : term924 _101211 _101227 t x' x => @lem3932226 _101211 _101227 x' t' a s t x h1). Qed.
Lemma lem3932229 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932230 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term998 _101211 _101227 t x' x) = (term897 _101211 _101227 t x' x).
Proof. exact (@lem3932229 (term897 _101211 _101227 t x' x)). Qed.
Lemma lem3932231 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term897 _101211 _101227 t x' x.
Proof. exact (EQ_MP (@lem3932230 _101211 _101227 t x' x) (@lem3932227 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932233 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932234 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term1003 _101211 _101227 t _45669 _45668 x) = (term1004 _101211 _101227 t _45669 _45668 x).
Proof. exact (@lem3932233 (_45668 = (@I (_101227 -> _101211 -> Prop) t _45669)) (@I (_101211 -> Prop) _45668 x)). Qed.
Lemma lem3932235 {_101227 : Type'} (s : _101227 -> Prop) (_45669 : _101227) : (term915 _101227 s _45669) = (term915 _101227 s _45669).
Proof. exact (eq_refl (term915 _101227 s _45669)). Qed.
Lemma lem3932236 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45669 _45668 x) = (term1005 _101211 _101227 s t _45669 _45668 x).
Proof. exact (MK_COMB (@lem3932235 _101227 s _45669) (@lem3932234 _101211 _101227 t _45669 _45668 x)). Qed.
Lemma lem3932238 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932239 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term1005 _101211 _101227 s t _45669 _45668 x) = (term1006 _101211 _101227 s t _45669 _45668 x).
Proof. exact (@lem3932238 (@I (_101227 -> Prop) s _45669) (term1007 _101211 _101227 t _45669 _45668 x)). Qed.
Lemma lem3932240 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45669 _45668 x) = (term1006 _101211 _101227 s t _45669 _45668 x).
Proof. exact (TRANS (@lem3932236 _101211 _101227 s t _45669 _45668 x) (@lem3932239 _101211 _101227 s t _45669 _45668 x)). Qed.
Lemma lem3932242 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3932243 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term1006 _101211 _101227 s t _45669 _45668 x) = (term1008 _101211 _101227 s t _45669 _45668 x).
Proof. exact (@lem3932242 (term1009 _101211 _101227 s t _45669 _45668 x)). Qed.
Lemma lem3932244 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45669 : _101227) (_45668 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45669 _45668 x) = (term1008 _101211 _101227 s t _45669 _45668 x).
Proof. exact (TRANS (@lem3932240 _101211 _101227 s t _45669 _45668 x) (@lem3932243 _101211 _101227 s t _45669 _45668 x)). Qed.
Lemma lem3932246 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term1010 _101211 _101227 t x' x.
Proof. exact (conj (@lem3932224 _101211 _101227 t x') (@lem3932231 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932247 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : term1011 _101211 _101227 s t x' x.
Proof. exact (conj (@lem3932215 _101227 s x' h2) (@lem3932246 _101211 _101227 x' t' a s t x h1)). Qed.
Lemma lem3932249 {_101211 _101227 : Type'} (_45669 : _101227) (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term1008 _101211 _101227 s t _45669 _45668 x.
Proof. exact (EQ_MP (@lem3932244 _101211 _101227 s t _45669 _45668 x) (@lem3931963 _101211 _101227 _45669 _45668 x' t' a s t x h1)). Qed.
Lemma lem3932250 {_101211 _101227 : Type'} (_45669 : _101227) (_45668 : _101211 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term1008 _101211 _101227 s t _45669 _45668 x.
Proof. exact (@lem3932249 _101211 _101227 _45669 _45668 x' t' a s t x h1). Qed.
Lemma lem3932251 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : term1012 _101211 _101227 s t x' x.
Proof. exact (@lem3932250 _101211 _101227 x' (@I (_101227 -> _101211 -> Prop) t x') x' t' a s t x h1). Qed.
Lemma lem3932254 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (@lem3932251 _101211 _101227 x' t' a s t x h1 (@lem3932247 _101211 _101227 t' a t x s x' h1 h2)). Qed.
Lemma lem3932255 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : term482.
Proof. exact (fun h0 : ~ False => @lem3932254 _101211 _101227 t' a t x s x' h1 h2). Qed.
Lemma lem3932257 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932258 : term482 = False.
Proof. exact (@lem3932257 False). Qed.
Lemma lem3932259 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3932258) (@lem3932255 _101211 _101227 t' a t x s x' h1 h2)). Qed.
Lemma lem3932324 {_101227 : Type'} (x : _101227) : x = x.
Proof. exact (@lem21386 _101227 x). Qed.
Lemma lem3932325 {_101227 : Type'} (x : _101227) : x = x.
Proof. exact (@lem3932324 _101227 x). Qed.
Lemma lem3932326 {_101227 : Type'} (a : _101227) : a = a.
Proof. exact (@lem3932325 _101227 a). Qed.
Lemma lem3932327 {_101227 : Type'} (a : _101227) : term1013 _101227 a.
Proof. exact (fun h0 : term1014 _101227 a => @lem3932326 _101227 a). Qed.
Lemma lem3932329 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932330 {_101227 : Type'} (a : _101227) : (term1013 _101227 a) = (a = a).
Proof. exact (@lem3932329 (a = a)). Qed.
Lemma lem3932331 {_101227 : Type'} (a : _101227) : a = a.
Proof. exact (EQ_MP (@lem3932330 _101227 a) (@lem3932327 _101227 a)). Qed.
Lemma lem3932333 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem21386 (_101211 -> Prop) x). Qed.
Lemma lem3932334 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem3932333 _101211 x). Qed.
Lemma lem3932335 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : (@I (_101227 -> _101211 -> Prop) t a) = (@I (_101227 -> _101211 -> Prop) t a).
Proof. exact (@lem3932334 _101211 (@I (_101227 -> _101211 -> Prop) t a)). Qed.
Lemma lem3932336 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : term1001 _101211 _101227 t a.
Proof. exact (fun h0 : term1002 _101211 _101227 t a => @lem3932335 _101211 _101227 t a). Qed.
Lemma lem3932338 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932339 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : (term1001 _101211 _101227 t a) = ((@I (_101227 -> _101211 -> Prop) t a) = (@I (_101227 -> _101211 -> Prop) t a)).
Proof. exact (@lem3932338 ((@I (_101227 -> _101211 -> Prop) t a) = (@I (_101227 -> _101211 -> Prop) t a))). Qed.
Lemma lem3932340 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) : (@I (_101227 -> _101211 -> Prop) t a) = (@I (_101227 -> _101211 -> Prop) t a).
Proof. exact (EQ_MP (@lem3932339 _101211 _101227 t a) (@lem3932336 _101211 _101227 t a)). Qed.
Lemma lem3932342 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term897 _101211 _101227 t a x.
Proof. exact (h1). Qed.
Lemma lem3932343 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term998 _101211 _101227 t a x.
Proof. exact (fun h0 : term924 _101211 _101227 t a x => @lem3932342 _101211 _101227 t a x h1). Qed.
Lemma lem3932345 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932346 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) : (term998 _101211 _101227 t a x) = (term897 _101211 _101227 t a x).
Proof. exact (@lem3932345 (term897 _101211 _101227 t a x)). Qed.
Lemma lem3932347 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term897 _101211 _101227 t a x.
Proof. exact (EQ_MP (@lem3932346 _101211 _101227 t a x) (@lem3932343 _101211 _101227 t a x h1)). Qed.
Lemma lem3932349 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932350 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term1003 _101211 _101227 t _45671 _45670 x) = (term1004 _101211 _101227 t _45671 _45670 x).
Proof. exact (@lem3932349 (_45670 = (@I (_101227 -> _101211 -> Prop) t _45671)) (@I (_101211 -> Prop) _45670 x)). Qed.
Lemma lem3932351 {_101227 : Type'} (_45671 : _101227) (a : _101227) : (term1015 _101227 _45671 a) = (term1015 _101227 _45671 a).
Proof. exact (eq_refl (term1015 _101227 _45671 a)). Qed.
Lemma lem3932352 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term988 _101211 _101227 a t _45671 _45670 x) = (term1016 _101211 _101227 a t _45671 _45670 x).
Proof. exact (MK_COMB (@lem3932351 _101227 _45671 a) (@lem3932350 _101211 _101227 t _45671 _45670 x)). Qed.
Lemma lem3932354 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932355 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term1016 _101211 _101227 a t _45671 _45670 x) = (term1017 _101211 _101227 a t _45671 _45670 x).
Proof. exact (@lem3932354 (_45671 = a) (term1007 _101211 _101227 t _45671 _45670 x)). Qed.
Lemma lem3932356 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term988 _101211 _101227 a t _45671 _45670 x) = (term1017 _101211 _101227 a t _45671 _45670 x).
Proof. exact (TRANS (@lem3932352 _101211 _101227 a t _45671 _45670 x) (@lem3932355 _101211 _101227 a t _45671 _45670 x)). Qed.
Lemma lem3932358 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3932359 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term1017 _101211 _101227 a t _45671 _45670 x) = (term1018 _101211 _101227 a t _45671 _45670 x).
Proof. exact (@lem3932358 (term1019 _101211 _101227 a t _45671 _45670 x)). Qed.
Lemma lem3932360 {_101211 _101227 : Type'} (a : _101227) (t : type1470 _101211 _101227) (_45671 : _101227) (_45670 : _101211 -> Prop) (x : _101211) : (term988 _101211 _101227 a t _45671 _45670 x) = (term1018 _101211 _101227 a t _45671 _45670 x).
Proof. exact (TRANS (@lem3932356 _101211 _101227 a t _45671 _45670 x) (@lem3932359 _101211 _101227 a t _45671 _45670 x)). Qed.
Lemma lem3932362 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term1010 _101211 _101227 t a x.
Proof. exact (conj (@lem3932340 _101211 _101227 t a) (@lem3932347 _101211 _101227 t a x h1)). Qed.
Lemma lem3932363 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term897 _101211 _101227 t a x) : term1020 _101211 _101227 t a x.
Proof. exact (conj (@lem3932331 _101227 a) (@lem3932362 _101211 _101227 t a x h1)). Qed.
Lemma lem3932365 {_101211 _101227 : Type'} (_45671 : _101227) (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1018 _101211 _101227 a t _45671 _45670 x.
Proof. exact (EQ_MP (@lem3932360 _101211 _101227 a t _45671 _45670 x) (@lem3931755 _101211 _101227 _45671 _45670 a s t x' t' x h1)). Qed.
Lemma lem3932366 {_101211 _101227 : Type'} (_45671 : _101227) (_45670 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1018 _101211 _101227 a t _45671 _45670 x.
Proof. exact (@lem3932365 _101211 _101227 _45671 _45670 a s t x' t' x h1). Qed.
Lemma lem3932367 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1021 _101211 _101227 t a x.
Proof. exact (@lem3932366 _101211 _101227 a (@I (_101227 -> _101211 -> Prop) t a) a s t x' t' x h1). Qed.
Lemma lem3932370 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : False.
Proof. exact (@lem3932367 _101211 _101227 a s t x' t' x h1 (@lem3932363 _101211 _101227 t a x h2)). Qed.
Lemma lem3932371 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : term482.
Proof. exact (fun h0 : ~ False => @lem3932370 _101211 _101227 s x' t' t a x h1 h2). Qed.
Lemma lem3932373 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932374 : term482 = False.
Proof. exact (@lem3932373 False). Qed.
Lemma lem3932375 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : False.
Proof. exact (EQ_MP (@lem3932374) (@lem3932371 _101211 _101227 s x' t' t a x h1 h2)). Qed.
Lemma lem3932440 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : @I (_101227 -> Prop) s x'.
Proof. exact (proj1 (@lem3931399 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932441 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term1000 _101227 s x'.
Proof. exact (fun h0 : term900 _101227 s x' => @lem3932440 _101211 _101227 s t x' t' x h1). Qed.
Lemma lem3932443 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932444 {_101227 : Type'} (s : _101227 -> Prop) (x' : _101227) : (term1000 _101227 s x') = (@I (_101227 -> Prop) s x').
Proof. exact (@lem3932443 (@I (_101227 -> Prop) s x')). Qed.
Lemma lem3932445 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : @I (_101227 -> Prop) s x'.
Proof. exact (EQ_MP (@lem3932444 _101227 s x') (@lem3932441 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932447 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem21386 (_101211 -> Prop) x). Qed.
Lemma lem3932448 {_101211 : Type'} (x : _101211 -> Prop) : x = x.
Proof. exact (@lem3932447 _101211 x). Qed.
Lemma lem3932449 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (@lem3932448 _101211 (@I (_101227 -> _101211 -> Prop) t x')). Qed.
Lemma lem3932450 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : term1001 _101211 _101227 t x'.
Proof. exact (fun h0 : term1002 _101211 _101227 t x' => @lem3932449 _101211 _101227 t x'). Qed.
Lemma lem3932452 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932453 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (term1001 _101211 _101227 t x') = ((@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x')).
Proof. exact (@lem3932452 ((@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x'))). Qed.
Lemma lem3932454 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) : (@I (_101227 -> _101211 -> Prop) t x') = (@I (_101227 -> _101211 -> Prop) t x').
Proof. exact (EQ_MP (@lem3932453 _101211 _101227 t x') (@lem3932450 _101211 _101227 t x')). Qed.
Lemma lem3932456 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term897 _101211 _101227 t x' x.
Proof. exact (EQ_MP (@lem3932016 _101211 _101227 s t x' t' x h1) (@lem3931769 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932457 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term998 _101211 _101227 t x' x.
Proof. exact (fun h0 : term924 _101211 _101227 t x' x => @lem3932456 _101211 _101227 s t x' t' x h1). Qed.
Lemma lem3932459 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932460 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (x' : _101227) (x : _101211) : (term998 _101211 _101227 t x' x) = (term897 _101211 _101227 t x' x).
Proof. exact (@lem3932459 (term897 _101211 _101227 t x' x)). Qed.
Lemma lem3932461 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term897 _101211 _101227 t x' x.
Proof. exact (EQ_MP (@lem3932460 _101211 _101227 t x' x) (@lem3932457 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932463 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932464 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term1003 _101211 _101227 t _45673 _45672 x) = (term1004 _101211 _101227 t _45673 _45672 x).
Proof. exact (@lem3932463 (_45672 = (@I (_101227 -> _101211 -> Prop) t _45673)) (@I (_101211 -> Prop) _45672 x)). Qed.
Lemma lem3932465 {_101227 : Type'} (s : _101227 -> Prop) (_45673 : _101227) : (term915 _101227 s _45673) = (term915 _101227 s _45673).
Proof. exact (eq_refl (term915 _101227 s _45673)). Qed.
Lemma lem3932466 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45673 _45672 x) = (term1005 _101211 _101227 s t _45673 _45672 x).
Proof. exact (MK_COMB (@lem3932465 _101227 s _45673) (@lem3932464 _101211 _101227 t _45673 _45672 x)). Qed.
Lemma lem3932468 (a : Prop) (b : Prop) : (term475 a b) = (term476 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3932469 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term1005 _101211 _101227 s t _45673 _45672 x) = (term1006 _101211 _101227 s t _45673 _45672 x).
Proof. exact (@lem3932468 (@I (_101227 -> Prop) s _45673) (term1007 _101211 _101227 t _45673 _45672 x)). Qed.
Lemma lem3932470 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45673 _45672 x) = (term1006 _101211 _101227 s t _45673 _45672 x).
Proof. exact (TRANS (@lem3932466 _101211 _101227 s t _45673 _45672 x) (@lem3932469 _101211 _101227 s t _45673 _45672 x)). Qed.
Lemma lem3932472 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3932473 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term1006 _101211 _101227 s t _45673 _45672 x) = (term1008 _101211 _101227 s t _45673 _45672 x).
Proof. exact (@lem3932472 (term1009 _101211 _101227 s t _45673 _45672 x)). Qed.
Lemma lem3932474 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (_45673 : _101227) (_45672 : _101211 -> Prop) (x : _101211) : (term987 _101211 _101227 s t _45673 _45672 x) = (term1008 _101211 _101227 s t _45673 _45672 x).
Proof. exact (TRANS (@lem3932470 _101211 _101227 s t _45673 _45672 x) (@lem3932473 _101211 _101227 s t _45673 _45672 x)). Qed.
Lemma lem3932476 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term1010 _101211 _101227 t x' x.
Proof. exact (conj (@lem3932454 _101211 _101227 t x') (@lem3932461 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932477 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term896 _101211 _101227 s t x' t' x) : term1011 _101211 _101227 s t x' x.
Proof. exact (conj (@lem3932445 _101211 _101227 s t x' t' x h1) (@lem3932476 _101211 _101227 s t x' t' x h1)). Qed.
Lemma lem3932479 {_101211 _101227 : Type'} (_45673 : _101227) (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1008 _101211 _101227 s t _45673 _45672 x.
Proof. exact (EQ_MP (@lem3932474 _101211 _101227 s t _45673 _45672 x) (@lem3932059 _101211 _101227 _45673 _45672 a s t x' t' x h1)). Qed.
Lemma lem3932480 {_101211 _101227 : Type'} (_45673 : _101227) (_45672 : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1008 _101211 _101227 s t _45673 _45672 x.
Proof. exact (@lem3932479 _101211 _101227 _45673 _45672 a s t x' t' x h1). Qed.
Lemma lem3932481 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : term1012 _101211 _101227 s t x' x.
Proof. exact (@lem3932480 _101211 _101227 x' (@I (_101227 -> _101211 -> Prop) t x') a s t x' t' x h1). Qed.
Lemma lem3932484 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term896 _101211 _101227 s t x' t' x) : False.
Proof. exact (@lem3932481 _101211 _101227 a s t x' t' x h1 (@lem3932477 _101211 _101227 s t x' t' x h2)). Qed.
Lemma lem3932485 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term896 _101211 _101227 s t x' t' x) : term482.
Proof. exact (fun h0 : ~ False => @lem3932484 _101211 _101227 a s t x' t' x h1 h2). Qed.
Lemma lem3932487 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3932488 : term482 = False.
Proof. exact (@lem3932487 False). Qed.
Lemma lem3932490 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term896 _101211 _101227 s t x' t' x) : False.
Proof. exact (EQ_MP (@lem3932488) (@lem3932485 _101211 _101227 a s t x' t' x h1 h2)). Qed.
Lemma lem3932491 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : (@I (_101227 -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (_101227 -> Prop) s x' => @lem3932259 _101211 _101227 t' a t x s x' h1 h2) (fun h3 : False => @lem3931990 _101227 s x' h2)). Qed.
Lemma lem3932493 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3932491 _101211 _101227 t' a t x s x' h1 h2) (@lem3931990 _101227 s x' h2)). Qed.
Lemma lem3932495 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3932144) (@lem3932141 _101211 _101227 t' s t x x' a h1 h2)). Qed.
Lemma lem3932496 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : (term897 _101211 _101227 t a x) = False.
Proof. exact (prop_ext (fun h3 : term897 _101211 _101227 t a x => @lem3932375 _101211 _101227 s x' t' t a x h1 h2) (fun h3 : False => @lem3931743 _101211 _101227 t a x h2)). Qed.
Lemma lem3932497 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : False.
Proof. exact (EQ_MP (@lem3932496 _101211 _101227 s x' t' t a x h1 h2) (@lem3931743 _101211 _101227 t a x h2)). Qed.
Lemma lem3932498 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : (@I (_101227 -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (_101227 -> Prop) s x' => @lem3932493 _101211 _101227 t' a t x s x' h1 h2) (fun h3 : False => @lem3931741 _101227 s x' h2)). Qed.
Lemma lem3932499 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3932498 _101211 _101227 t' a t x s x' h1 h2) (@lem3931741 _101227 s x' h2)). Qed.
Lemma lem3932500 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3932495 _101211 _101227 t' s t x x' a h1 h2) (fun h3 : False => @lem3931721 _101227 x' a h2)). Qed.
Lemma lem3932501 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3932500 _101211 _101227 t' s t x x' a h1 h2) (@lem3931721 _101227 x' a h2)). Qed.
Lemma lem3932502 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : (term897 _101211 _101227 t a x) = False.
Proof. exact (prop_ext (fun h3 : term897 _101211 _101227 t a x => @lem3932497 _101211 _101227 s x' t' t a x h1 h2) (fun h3 : False => @lem3931597 _101211 _101227 t a x h2)). Qed.
Lemma lem3932503 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : False.
Proof. exact (EQ_MP (@lem3932502 _101211 _101227 s x' t' t a x h1 h2) (@lem3931597 _101211 _101227 t a x h2)). Qed.
Lemma lem3932504 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : (@I (_101227 -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (_101227 -> Prop) s x' => @lem3932499 _101211 _101227 t' a t x s x' h1 h2) (fun h3 : False => @lem3931529 _101227 s x' h2)). Qed.
Lemma lem3932505 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3932504 _101211 _101227 t' a t x s x' h1 h2) (@lem3931529 _101227 s x' h2)). Qed.
Lemma lem3932506 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3932501 _101211 _101227 t' s t x x' a h1 h2) (fun h3 : False => @lem3931465 _101227 x' a h2)). Qed.
Lemma lem3932507 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3932506 _101211 _101227 t' s t x x' a h1 h2) (@lem3931465 _101227 x' a h2)). Qed.
Lemma lem3932508 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : (term897 _101211 _101227 t a x) = False.
Proof. exact (prop_ext (fun h3 : term897 _101211 _101227 t a x => @lem3932503 _101211 _101227 s x' t' t a x h1 h2) (fun h3 : False => @lem3931597 _101211 _101227 t a x h2)). Qed.
Lemma lem3932509 {_101211 _101227 : Type'} (s : _101227 -> Prop) (x' : _101227) (t' : _101211 -> Prop) (t : type1470 _101211 _101227) (a : _101227) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) (h2 : term897 _101211 _101227 t a x) : False.
Proof. exact (EQ_MP (@lem3932508 _101211 _101227 s x' t' t a x h1 h2) (@lem3931597 _101211 _101227 t a x h2)). Qed.
Lemma lem3932510 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : (@I (_101227 -> Prop) s x') = False.
Proof. exact (prop_ext (fun h3 : @I (_101227 -> Prop) s x' => @lem3932505 _101211 _101227 t' a t x s x' h1 h2) (fun h3 : False => @lem3931529 _101227 s x' h2)). Qed.
Lemma lem3932511 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (a : _101227) (t : type1470 _101211 _101227) (x : _101211) (s : _101227 -> Prop) (x' : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : @I (_101227 -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3932510 _101211 _101227 t' a t x s x' h1 h2) (@lem3931529 _101227 s x' h2)). Qed.
Lemma lem3932512 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3932507 _101211 _101227 t' s t x x' a h1 h2) (fun h3 : False => @lem3931465 _101227 x' a h2)). Qed.
Lemma lem3932513 {_101211 _101227 : Type'} (t' : _101211 -> Prop) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (x' : _101227) (a : _101227) (h1 : term933 _101211 _101227 x' t' a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3932512 _101211 _101227 t' s t x x' a h1 h2) (@lem3931465 _101227 x' a h2)). Qed.
Lemma lem3932514 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term913 _101211 _101227 a s t x' t' x) : False.
Proof. exact (or_elim (@lem3931394 _101211 _101227 a s t x' t' x h1) (fun h0 : term897 _101211 _101227 t a x => @lem3932509 _101211 _101227 s x' t' t a x h1 h0) (fun h0 : term896 _101211 _101227 s t x' t' x => @lem3932490 _101211 _101227 a s t x' t' x h1 h0)). Qed.
Lemma lem3932515 {_101211 _101227 : Type'} (x' : _101227) (t' : _101211 -> Prop) (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term933 _101211 _101227 x' t' a s t x) : False.
Proof. exact (or_elim (@lem3931391 _101211 _101227 x' t' a s t x h1) (fun h0 : x' = a => @lem3932513 _101211 _101227 t' s t x x' a h1 h0) (fun h0 : @I (_101227 -> Prop) s x' => @lem3932511 _101211 _101227 t' a t x s x' h1 h0)). Qed.
Lemma lem3932516 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x' : _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term887 _101211 _101227 a s t x' t' x) : False.
Proof. exact (or_elim (@lem3931381 _101211 _101227 a s t x' t' x h1) (fun h0 : term933 _101211 _101227 x' t' a s t x => @lem3932515 _101211 _101227 x' t' a s t x h0) (fun h0 : term913 _101211 _101227 a s t x' t' x => @lem3932514 _101211 _101227 a s t x' t' x h0)). Qed.
Lemma lem3932517 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (t' : _101211 -> Prop) (x : _101211) (h1 : term890 _101211 _101227 a s t t' x) : False.
Proof. exact (ex_elim (@lem3931150 _101211 _101227 a s t t' x h1) (fun x' : _101227 => fun h0 : term889 _101211 _101227 a s t t' x x' => @lem3932516 _101211 _101227 a s t x' t' x h0)). Qed.
Lemma lem3932518 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term657 _101211 _101227 a s t x) : False.
Proof. exact (ex_elim (@lem3931149 _101211 _101227 a s t x h1) (fun t' : _101211 -> Prop => fun h0 : term891 _101211 _101227 a s t x t' => @lem3932517 _101211 _101227 a s t t' x h0)). Qed.
Lemma lem3932519 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term657 _101211 _101227 a s t x) : (term657 _101211 _101227 a s t x) = False.
Proof. exact (prop_ext (fun h2 : term657 _101211 _101227 a s t x => @lem3932518 _101211 _101227 a s t x h1) (fun h2 : False => @lem3930387 _101211 _101227 a s t x h1)). Qed.
Lemma lem3932520 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) (h1 : term657 _101211 _101227 a s t x) : False.
Proof. exact (EQ_MP (@lem3932519 _101211 _101227 a s t x h1) (@lem3930387 _101211 _101227 a s t x h1)). Qed.
Lemma lem3932521 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : term656 _101211 _101227 a s t x.
Proof. exact (fun h0 : term657 _101211 _101227 a s t x => @lem3932520 _101211 _101227 a s t x h0). Qed.
Lemma lem3932522 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (x : _101211) : (term582 _101211 _101227 a s t x) = (term634 _101211 _101227 a s t x).
Proof. exact (EQ_MP (@lem3930386 _101211 _101227 a s t x) (@lem3932521 _101211 _101227 a s t x)). Qed.
Lemma lem3932527 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term637 _101211 _101227 a s t.
Proof. exact (fun x : _101211 => @lem3932522 _101211 _101227 a s t x). Qed.
Lemma lem3932532 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term647 _101211 _101227 s t.
Proof. exact (fun a : _101227 => @lem3932527 _101211 _101227 a s t). Qed.
Lemma lem3932537 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : term651 _101211 _101227 t.
Proof. exact (fun s : _101227 -> Prop => @lem3932532 _101211 _101227 s t). Qed.
Lemma lem3932542 {_101211 _101227 : Type'} : term655 _101211 _101227.
Proof. exact (fun t : type1470 _101211 _101227 => @lem3932537 _101211 _101227 t). Qed.
Lemma lem3932543 {_101211 _101227 : Type'} : term654 _101211 _101227.
Proof. exact (EQ_MP (@lem3930382 _101211 _101227) (@lem3932542 _101211 _101227)). Qed.
Lemma lem3932544 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : term1022 _101211 _101227 t.
Proof. exact (@lem3932543 _101211 _101227 t). Qed.
Lemma lem3932545 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : (term1022 _101211 _101227 t) = (term650 _101211 _101227 t).
Proof. exact (eq_refl (term1022 _101211 _101227 t)). Qed.
Lemma lem3932546 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) : term650 _101211 _101227 t.
Proof. exact (EQ_MP (@lem3932545 _101211 _101227 t) (@lem3932544 _101211 _101227 t)). Qed.
Lemma lem3932547 {_101211 _101227 : Type'} (t : type1470 _101211 _101227) (s : _101227 -> Prop) : term1023 _101211 _101227 t s.
Proof. exact (@lem3932546 _101211 _101227 t s). Qed.
Lemma lem3932548 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term1023 _101211 _101227 t s) = (term646 _101211 _101227 s t).
Proof. exact (eq_refl (term1023 _101211 _101227 t s)). Qed.
Lemma lem3932549 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term646 _101211 _101227 s t.
Proof. exact (EQ_MP (@lem3932548 _101211 _101227 s t) (@lem3932547 _101211 _101227 t s)). Qed.
Lemma lem3932550 {_101211 _101227 : Type'} (s : _101227 -> Prop) (t : type1470 _101211 _101227) (a : _101227) : term1024 _101211 _101227 s t a.
Proof. exact (@lem3932549 _101211 _101227 s t a). Qed.
Lemma lem3932551 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term1024 _101211 _101227 s t a) = (term638 _101211 _101227 a s t).
Proof. exact (eq_refl (term1024 _101211 _101227 s t a)). Qed.
Lemma lem3932552 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term638 _101211 _101227 a s t.
Proof. exact (EQ_MP (@lem3932551 _101211 _101227 a s t) (@lem3932550 _101211 _101227 s t a)). Qed.
Lemma lem3932554 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term638 _101211 _101227 a s t.
Proof. exact (@lem3930033 _101211 _101227 a s t (@lem3932552 _101211 _101227 a s t)). Qed.
Lemma lem3932555 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term639 _101211 _101227 a s t) : False.
Proof. exact (@lem3932554 _101211 _101227 a s t (@lem3930017 _101211 _101227 a s t h1)). Qed.
Lemma lem3932556 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term639 _101211 _101227 a s t) : (term639 _101211 _101227 a s t) = False.
Proof. exact (prop_ext (fun h2 : term639 _101211 _101227 a s t => @lem3932555 _101211 _101227 a s t h1) (fun h2 : False => @lem3930017 _101211 _101227 a s t h1)). Qed.
Lemma lem3932557 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) (h1 : term639 _101211 _101227 a s t) : False.
Proof. exact (EQ_MP (@lem3932556 _101211 _101227 a s t h1) (@lem3930017 _101211 _101227 a s t h1)). Qed.
Lemma lem3932558 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term638 _101211 _101227 a s t.
Proof. exact (fun h0 : term639 _101211 _101227 a s t => @lem3932557 _101211 _101227 a s t h0). Qed.
Lemma lem3932559 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term637 _101211 _101227 a s t.
Proof. exact (EQ_MP (@lem3930016 _101211 _101227 a s t) (@lem3932558 _101211 _101227 a s t)). Qed.
Lemma lem3932560 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : term525 _101211 _101227 a s t.
Proof. exact (EQ_MP (@lem3930012 _101211 _101227 a s t) (@lem3932559 _101211 _101227 a s t)). Qed.
Lemma lem3932575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term300 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3932576 {_101251 : Type'} (s : _101251 -> Prop) (t : _101251 -> Prop) : (s = t) = (term300 _101251 s t).
Proof. exact (@lem3932575 _101251 s t). Qed.
Lemma lem3932577 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : ((term1025 _101250 _101251 t) = (@EMPTY _101251)) = (term1026 _101250 _101251 t).
Proof. exact (@lem3932576 _101251 (term1025 _101250 _101251 t) (@EMPTY _101251)). Qed.
Lemma lem3932590 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1026 _101250 _101251 t) = ((term1025 _101250 _101251 t) = (@EMPTY _101251)).
Proof. exact (SYM (@lem3932577 _101250 _101251 t)). Qed.
Lemma lem3932598 {A : Type'} (s : type686 A) (x : A) : (term526 A x s) = (term527 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3932599 {_101251 : Type'} (s : type686 _101251) (x : _101251) : (term526 _101251 x s) = (term527 _101251 s x).
Proof. exact (@lem3932598 _101251 s x). Qed.
Lemma lem3932600 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : (term1027 _101250 _101251 x t) = (term1028 _101250 _101251 t x).
Proof. exact (@lem3932599 _101251 (term1029 _101250 _101251 t) x). Qed.
Lemma lem3932610 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term303 _83064 x P) = (term304 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem3932611 {_101251 : Type'} (P : type909 _101251) (x : _101251 -> Prop) : (term531 _101251 x P) = (term532 _101251 P x).
Proof. exact (@lem3932610 (_101251 -> Prop) P x). Qed.
Lemma lem3932612 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (t' : _101251 -> Prop) : (term1030 _101250 _101251 t' t) = (term1031 _101250 _101251 t t').
Proof. exact (@lem3932611 _101251 (term1032 _101250 _101251 t) t'). Qed.
Lemma lem3932613 {_101250 _101251 : Type'} (GEN_PVAR_112 : _101251 -> Prop) (t : type1413 _101250 _101251) : (term1033 _101250 _101251 t GEN_PVAR_112) = (term1034 _101250 _101251 GEN_PVAR_112 t).
Proof. exact (eq_refl (term1033 _101250 _101251 t GEN_PVAR_112)). Qed.
Lemma lem3932614 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1035 _101250 _101251 t) = (term1036 _101250 _101251 t).
Proof. exact (fun_ext (fun GEN_PVAR_112 : _101251 -> Prop => @lem3932613 _101250 _101251 GEN_PVAR_112 t)). Qed.
Lemma lem3932615 {_101251 : Type'} : (@GSPEC (_101251 -> Prop)) = (@GSPEC (_101251 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_101251 -> Prop))). Qed.
Lemma lem3932616 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1037 _101250 _101251 t) = (term1029 _101250 _101251 t).
Proof. exact (MK_COMB (@lem3932615 _101251) (@lem3932614 _101250 _101251 t)). Qed.
Lemma lem3932617 {_101251 : Type'} (t : _101251 -> Prop) : (@IN (_101251 -> Prop) t) = (@IN (_101251 -> Prop) t).
Proof. exact (eq_refl (@IN (_101251 -> Prop) t)). Qed.
Lemma lem3932618 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1030 _101250 _101251 t t') = (term1038 _101250 _101251 t t').
Proof. exact (MK_COMB (@lem3932617 _101251 t) (@lem3932616 _101250 _101251 t')). Qed.
Lemma lem3932619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3932620 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1039 _101250 _101251 t t') = (term1040 _101250 _101251 t t').
Proof. exact (MK_COMB (@lem3932619) (@lem3932618 _101250 _101251 t t')). Qed.
Lemma lem3932621 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1031 _101250 _101251 t' t) = (term1041 _101250 _101251 t t').
Proof. exact (eq_refl (term1031 _101250 _101251 t' t)). Qed.
Lemma lem3932622 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : ((term1030 _101250 _101251 t t') = (term1031 _101250 _101251 t' t)) = ((term1038 _101250 _101251 t t') = (term1041 _101250 _101251 t t')).
Proof. exact (MK_COMB (@lem3932620 _101250 _101251 t t') (@lem3932621 _101250 _101251 t t')). Qed.
Lemma lem3932623 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1038 _101250 _101251 t t') = (term1041 _101250 _101251 t t').
Proof. exact (EQ_MP (@lem3932622 _101250 _101251 t t') (@lem3932612 _101250 _101251 t' t)). Qed.
Lemma lem3932629 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3932630 {_101251 : Type'} (f : type1527 _101251) (y : Prop) : (term545 _101251 f y) = (f y).
Proof. exact (@lem3932629 Prop (type686 _101251) f y). Qed.
Lemma lem3932631 {_101250 _101251 : Type'} (t : _101251 -> Prop) (x : _101250) : (term1042 _101250 _101251 t x) = (term1043 _101250 _101251 t x).
Proof. exact (@lem3932630 _101251 (term548 _101251 t) (@IN _101250 x (@EMPTY _101250))). Qed.
Lemma lem3932632 {_101251 : Type'} (p : Prop) (t : _101251 -> Prop) : (term550 _101251 t p) = (term551 _101251 p t).
Proof. exact (eq_refl (term550 _101251 t p)). Qed.
Lemma lem3932633 {_101251 : Type'} (t : _101251 -> Prop) : (term552 _101251 t) = (term548 _101251 t).
Proof. exact (fun_ext (fun p : Prop => @lem3932632 _101251 p t)). Qed.
Lemma lem3932634 {_101250 : Type'} (x : _101250) : (@IN _101250 x (@EMPTY _101250)) = (@IN _101250 x (@EMPTY _101250)).
Proof. exact (eq_refl (@IN _101250 x (@EMPTY _101250))). Qed.
Lemma lem3932635 {_101250 _101251 : Type'} (t : _101251 -> Prop) (x : _101250) : (term1042 _101250 _101251 t x) = (term1043 _101250 _101251 t x).
Proof. exact (MK_COMB (@lem3932633 _101251 t) (@lem3932634 _101250 x)). Qed.
Lemma lem3932636 {_101251 : Type'} : (@eq ((_101251 -> Prop) -> Prop)) = (@eq ((_101251 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_101251 -> Prop) -> Prop))). Qed.
Lemma lem3932637 {_101250 _101251 : Type'} (t : _101251 -> Prop) (x : _101250) : (term1044 _101250 _101251 t x) = (term1045 _101250 _101251 t x).
Proof. exact (MK_COMB (@lem3932636 _101251) (@lem3932635 _101250 _101251 t x)). Qed.
Lemma lem3932638 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) : (term1043 _101250 _101251 t x) = (term1046 _101250 _101251 x t).
Proof. exact (eq_refl (term1043 _101250 _101251 t x)). Qed.
Lemma lem3932639 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) : ((term1042 _101250 _101251 t x) = (term1043 _101250 _101251 t x)) = ((term1043 _101250 _101251 t x) = (term1046 _101250 _101251 x t)).
Proof. exact (MK_COMB (@lem3932637 _101250 _101251 t x) (@lem3932638 _101250 _101251 x t)). Qed.
Lemma lem3932640 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) : (term1043 _101250 _101251 t x) = (term1046 _101250 _101251 x t).
Proof. exact (EQ_MP (@lem3932639 _101250 _101251 x t) (@lem3932631 _101250 _101251 t x)). Qed.
Lemma lem3932644 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3932645 {_101250 : Type'} (x : _101250) : (@IN _101250 x (@EMPTY _101250)) = False.
Proof. exact (@lem3932644 _101250 x). Qed.
Lemma lem3932646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3932647 {_101250 : Type'} (x : _101250) : (term1047 _101250 x) = (and False).
Proof. exact (MK_COMB (@lem3932646) (@lem3932645 _101250 x)). Qed.
Lemma lem3932650 {_101251 : Type'} (t : _101251 -> Prop) (t' : _101251 -> Prop) : (t = t') = (t = t').
Proof. exact (eq_refl (t = t')). Qed.
Lemma lem3932651 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) (t' : _101251 -> Prop) : (term1048 _101250 _101251 x t t') = (term1049 _101251 t t').
Proof. exact (MK_COMB (@lem3932647 _101250 x) (@lem3932650 _101251 t t')). Qed.
Lemma lem3932653 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3932654 {_101251 : Type'} (t : _101251 -> Prop) (t' : _101251 -> Prop) : (term1049 _101251 t t') = False.
Proof. exact (@lem3932653 (t = t')). Qed.
Lemma lem3932655 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) (t' : _101251 -> Prop) : (term1048 _101250 _101251 x t t') = False.
Proof. exact (TRANS (@lem3932651 _101250 _101251 x t t') (@lem3932654 _101251 t t')). Qed.
Lemma lem3932656 {_101250 _101251 : Type'} (x : _101250) (t : _101251 -> Prop) : (term1046 _101250 _101251 x t) = (term1050 _101251).
Proof. exact (fun_ext (fun t' : _101251 -> Prop => @lem3932655 _101250 _101251 x t t')). Qed.
Lemma lem3932657 {_101250 _101251 : Type'} (t : _101251 -> Prop) (x : _101250) : (term1043 _101250 _101251 t x) = (term1050 _101251).
Proof. exact (TRANS (@lem3932640 _101250 _101251 x t) (@lem3932656 _101250 _101251 x t)). Qed.
Lemma lem3932658 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3932659 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) (x : _101250) : (term1051 _101250 _101251 t t' x) = (term1052 _101250 _101251 t' x).
Proof. exact (MK_COMB (@lem3932657 _101250 _101251 t x) (@lem3932658 _101250 _101251 t' x)). Qed.
Lemma lem3932661 {A B : Type'} (f : A -> B) (y : A) : (term317 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3932662 {_101251 : Type'} (f : type686 _101251) (y : _101251 -> Prop) : (term566 _101251 f y) = (f y).
Proof. exact (@lem3932661 (_101251 -> Prop) Prop f y). Qed.
Lemma lem3932663 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (term1053 _101250 _101251 t x) = (term1052 _101250 _101251 t x).
Proof. exact (@lem3932662 _101251 (term1050 _101251) (t x)). Qed.
Lemma lem3932664 {_101251 : Type'} (t' : _101251 -> Prop) : (term1054 _101251 t') = False.
Proof. exact (eq_refl (term1054 _101251 t')). Qed.
Lemma lem3932665 {_101251 : Type'} : (term1055 _101251) = (term1050 _101251).
Proof. exact (fun_ext (fun t' : _101251 -> Prop => @lem3932664 _101251 t')). Qed.
Lemma lem3932666 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3932667 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (term1053 _101250 _101251 t x) = (term1052 _101250 _101251 t x).
Proof. exact (MK_COMB (@lem3932665 _101251) (@lem3932666 _101250 _101251 t x)). Qed.
Lemma lem3932668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3932669 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (term1056 _101250 _101251 t x) = (term1057 _101250 _101251 t x).
Proof. exact (MK_COMB (@lem3932668) (@lem3932667 _101250 _101251 t x)). Qed.
Lemma lem3932670 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (term1052 _101250 _101251 t x) = False.
Proof. exact (eq_refl (term1052 _101250 _101251 t x)). Qed.
Lemma lem3932671 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : ((term1053 _101250 _101251 t x) = (term1052 _101250 _101251 t x)) = ((term1052 _101250 _101251 t x) = False).
Proof. exact (MK_COMB (@lem3932669 _101250 _101251 t x) (@lem3932670 _101250 _101251 t x)). Qed.
Lemma lem3932672 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101250) : (term1052 _101250 _101251 t x) = False.
Proof. exact (EQ_MP (@lem3932671 _101250 _101251 t x) (@lem3932663 _101250 _101251 t x)). Qed.
Lemma lem3932673 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) (x : _101250) : (term1051 _101250 _101251 t t' x) = False.
Proof. exact (TRANS (@lem3932659 _101250 _101251 t t' x) (@lem3932672 _101250 _101251 t' x)). Qed.
Lemma lem3932674 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1058 _101250 _101251 t t') = (term1059 _101250).
Proof. exact (fun_ext (fun x : _101250 => @lem3932673 _101250 _101251 t t' x)). Qed.
Lemma lem3932675 {_101250 : Type'} : (@ex _101250) = (@ex _101250).
Proof. exact (eq_refl (@ex _101250)). Qed.
Lemma lem3932676 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1041 _101250 _101251 t t') = (term1060 _101250).
Proof. exact (MK_COMB (@lem3932675 _101250) (@lem3932674 _101250 _101251 t t')). Qed.
Lemma lem3932678 {A : Type'} (t : Prop) : (term1061 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3932679 {_101250 : Type'} (t : Prop) : (term1061 _101250 t) = t.
Proof. exact (@lem3932678 _101250 t). Qed.
Lemma lem3932680 {_101250 : Type'} : (term1060 _101250) = False.
Proof. exact (@lem3932679 _101250 False). Qed.
Lemma lem3932681 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1041 _101250 _101251 t t') = False.
Proof. exact (TRANS (@lem3932676 _101250 _101251 t t') (@lem3932680 _101250)). Qed.
Lemma lem3932682 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1038 _101250 _101251 t t') = False.
Proof. exact (TRANS (@lem3932623 _101250 _101251 t t') (@lem3932681 _101250 _101251 t t')). Qed.
Lemma lem3932683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3932684 {_101250 _101251 : Type'} (t : _101251 -> Prop) (t' : type1413 _101250 _101251) : (term1062 _101250 _101251 t t') = (and False).
Proof. exact (MK_COMB (@lem3932683) (@lem3932682 _101250 _101251 t t')). Qed.
Lemma lem3932686 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3932687 {_101251 : Type'} (P : _101251 -> Prop) (x : _101251) : (@IN _101251 x P) = (P x).
Proof. exact (@lem3932686 _101251 P x). Qed.
Lemma lem3932688 {_101251 : Type'} (t : _101251 -> Prop) (x : _101251) : (@IN _101251 x t) = (t x).
Proof. exact (@lem3932687 _101251 t x). Qed.
Lemma lem3932689 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (t' : _101251 -> Prop) (x : _101251) : (term1063 _101250 _101251 t x t') = (term1064 _101251 t' x).
Proof. exact (MK_COMB (@lem3932684 _101250 _101251 t' t) (@lem3932688 _101251 t' x)). Qed.
Lemma lem3932691 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3932692 {_101251 : Type'} (t : _101251 -> Prop) (x : _101251) : (term1064 _101251 t x) = False.
Proof. exact (@lem3932691 (t x)). Qed.
Lemma lem3932693 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) (t' : _101251 -> Prop) : (term1063 _101250 _101251 t x t') = False.
Proof. exact (TRANS (@lem3932689 _101250 _101251 t t' x) (@lem3932692 _101251 t' x)). Qed.
Lemma lem3932694 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : (term1065 _101250 _101251 t x) = (term1050 _101251).
Proof. exact (fun_ext (fun t' : _101251 -> Prop => @lem3932693 _101250 _101251 t x t')). Qed.
Lemma lem3932695 {_101251 : Type'} : (@ex (_101251 -> Prop)) = (@ex (_101251 -> Prop)).
Proof. exact (eq_refl (@ex (_101251 -> Prop))). Qed.
Lemma lem3932696 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : (term1028 _101250 _101251 t x) = (term1066 _101251).
Proof. exact (MK_COMB (@lem3932695 _101251) (@lem3932694 _101250 _101251 t x)). Qed.
Lemma lem3932698 {A : Type'} (t : Prop) : (term1061 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem3932699 {_101251 : Type'} (t : Prop) : (term1067 _101251 t) = t.
Proof. exact (@lem3932698 (_101251 -> Prop) t). Qed.
Lemma lem3932700 {_101251 : Type'} : (term1066 _101251) = False.
Proof. exact (@lem3932699 _101251 False). Qed.
Lemma lem3932701 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : (term1028 _101250 _101251 t x) = False.
Proof. exact (TRANS (@lem3932696 _101250 _101251 t x) (@lem3932700 _101251)). Qed.
Lemma lem3932702 {_101250 _101251 : Type'} (x : _101251) (t : type1413 _101250 _101251) : (term1027 _101250 _101251 x t) = False.
Proof. exact (TRANS (@lem3932600 _101250 _101251 t x) (@lem3932701 _101250 _101251 t x)). Qed.
Lemma lem3932703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3932704 {_101250 _101251 : Type'} (x : _101251) (t : type1413 _101250 _101251) : (term1068 _101250 _101251 x t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3932703) (@lem3932702 _101250 _101251 x t)). Qed.
Lemma lem3932706 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3932707 {_101251 : Type'} (x : _101251) : (@IN _101251 x (@EMPTY _101251)) = False.
Proof. exact (@lem3932706 _101251 x). Qed.
Lemma lem3932708 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : ((term1027 _101250 _101251 x t) = (@IN _101251 x (@EMPTY _101251))) = (False = False).
Proof. exact (MK_COMB (@lem3932704 _101250 _101251 x t) (@lem3932707 _101251 x)). Qed.
Lemma lem3932710 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3932711 : (False = False) = (~ False).
Proof. exact (@lem3932710 False). Qed.
Lemma lem3932713 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3932714 : (False = False) = True.
Proof. exact (TRANS (@lem3932711) (@lem3932713)). Qed.
Lemma lem3932715 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) (x : _101251) : ((term1027 _101250 _101251 x t) = (@IN _101251 x (@EMPTY _101251))) = True.
Proof. exact (TRANS (@lem3932708 _101250 _101251 t x) (@lem3932714)). Qed.
Lemma lem3932716 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1069 _101250 _101251 t) = (term1070 _101251).
Proof. exact (fun_ext (fun x : _101251 => @lem3932715 _101250 _101251 t x)). Qed.
Lemma lem3932717 {_101251 : Type'} : (@all _101251) = (@all _101251).
Proof. exact (eq_refl (@all _101251)). Qed.
Lemma lem3932718 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1026 _101250 _101251 t) = (term1071 _101251).
Proof. exact (MK_COMB (@lem3932717 _101251) (@lem3932716 _101250 _101251 t)). Qed.
Lemma lem3932720 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3932721 {_101251 : Type'} (t : Prop) : (term1072 _101251 t) = t.
Proof. exact (@lem3932720 _101251 t). Qed.
Lemma lem3932722 {_101251 : Type'} : (term1071 _101251) = True.
Proof. exact (@lem3932721 _101251 True). Qed.
Lemma lem3932723 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1026 _101250 _101251 t) = True.
Proof. exact (TRANS (@lem3932718 _101250 _101251 t) (@lem3932722 _101251)). Qed.
Lemma lem3932724 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : True = (term1026 _101250 _101251 t).
Proof. exact (SYM (@lem3932723 _101250 _101251 t)). Qed.
Lemma lem3932725 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : term1026 _101250 _101251 t.
Proof. exact (EQ_MP (@lem3932724 _101250 _101251 t) (@lem0)). Qed.
Lemma lem3932727 (n : nat) : term1073 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem3932728 (n : nat) : (term1073 n) = (term1074 n).
Proof. exact (eq_refl (term1073 n)). Qed.
Lemma lem3932729 (n : nat) : term1074 n.
Proof. exact (EQ_MP (@lem3932728 n) (@lem3932727 n)). Qed.
Lemma lem3932730 (n : nat) : (term1074 n) = ((term1074 n) = True).
Proof. exact (@lem7 (term1074 n)). Qed.
Lemma lem3932742 {A : Type'} (h1 : term1075 A) : term1075 A.
Proof. exact (h1). Qed.
Lemma lem3932743 {A : Type'} (P : type686 A) (h1 : term1075 A) : term1076 A P.
Proof. exact (@lem3932742 A h1 P). Qed.
Lemma lem3932744 {A : Type'} (P : type686 A) : (term1076 A P) = (term1077 A P).
Proof. exact (eq_refl (term1076 A P)). Qed.
Lemma lem3932745 {A : Type'} (P : type686 A) (h1 : term1075 A) : term1077 A P.
Proof. exact (EQ_MP (@lem3932744 A P) (@lem3932743 A P h1)). Qed.
Lemma lem3932746 {A : Type'} (P : type686 A) (h1 : term1078 A P) : term1078 A P.
Proof. exact (h1). Qed.
Lemma lem3932747 {A : Type'} (P : type686 A) (h1 : term1075 A) (h2 : term1078 A P) : term1079 A P.
Proof. exact (@lem3932745 A P h1 (@lem3932746 A P h2)). Qed.
Lemma lem3932748 {A : Type'} (P : type686 A) (h1 : term1078 A P) : term1080 A P.
Proof. exact (fun h0 : term1075 A => @lem3932747 A P h0 h1). Qed.
Lemma lem3932749 {A : Type'} (h1 : term1075 A) : term1075 A.
Proof. exact (h1). Qed.
Lemma lem3932750 {A : Type'} (P : type686 A) (h1 : term1075 A) (h2 : term1078 A P) : term1079 A P.
Proof. exact (@lem3932748 A P h2 (@lem3932749 A h1)). Qed.
Lemma lem3932751 {A : Type'} (P : type686 A) (h1 : term1075 A) : term1077 A P.
Proof. exact (fun h0 : term1078 A P => @lem3932750 A P h1 h0). Qed.
Lemma lem3932752 {A : Type'} (h1 : term1075 A) : term1075 A.
Proof. exact (fun P : type686 A => @lem3932751 A P h1). Qed.
Lemma lem3932753 {A : Type'} : term1081 A.
Proof. exact (fun h0 : term1075 A => @lem3932752 A h0). Qed.
Lemma lem3932754 {A : Type'} : term1075 A.
Proof. exact (@lem3932753 A (@lem3558722 A)). Qed.
Lemma lem3932755 {A : Type'} (P : type686 A) : term1076 A P.
Proof. exact (@lem3932754 A P). Qed.
Lemma lem3932756 {A : Type'} (P : type686 A) : (term1076 A P) = (term1077 A P).
Proof. exact (eq_refl (term1076 A P)). Qed.
Lemma lem3932758 {A : Type'} (P : Prop) : term1082 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3932759 {A : Type'} (P : Prop) : (term1082 A P) = (term1083 A P).
Proof. exact (eq_refl (term1082 A P)). Qed.
Lemma lem3932760 {A : Type'} (P : Prop) : term1083 A P.
Proof. exact (EQ_MP (@lem3932759 A P) (@lem3932758 A P)). Qed.
Lemma lem3932761 {A : Type'} (P : Prop) (Q : A -> Prop) : term1084 A P Q.
Proof. exact (@lem3932760 A P Q). Qed.
Lemma lem3932762 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1084 A P Q) = ((term1085 A P Q) = (term1086 A P Q)).
Proof. exact (eq_refl (term1084 A P Q)). Qed.
Lemma lem3932767 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1087 t1 t2 t3) = (term1088 t1 t2 t3)) : (term1087 t1 t2 t3) = (term1088 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3932768 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1087 t1 t2 t3) = (term1088 t1 t2 t3)) : (term1088 t1 t2 t3) = (term1087 t1 t2 t3).
Proof. exact (SYM (@lem3932767 t1 t2 t3 h1)). Qed.
Lemma lem3932769 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1088 t1 t2 t3) = (term1087 t1 t2 t3)) : (term1088 t1 t2 t3) = (term1087 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3932770 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1088 t1 t2 t3) = (term1087 t1 t2 t3)) : (term1087 t1 t2 t3) = (term1088 t1 t2 t3).
Proof. exact (SYM (@lem3932769 t1 t2 t3 h1)). Qed.
Lemma lem3932771 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term1087 t1 t2 t3) = (term1088 t1 t2 t3)) = ((term1088 t1 t2 t3) = (term1087 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term1087 t1 t2 t3) = (term1088 t1 t2 t3) => @lem3932768 t1 t2 t3 h1) (fun h1 : (term1088 t1 t2 t3) = (term1087 t1 t2 t3) => @lem3932770 t1 t2 t3 h1)). Qed.
Lemma lem3932772 (t1 : Prop) (t2 : Prop) : (term1089 t1 t2) = (term1090 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem3932771 t1 t2 t3)). Qed.
Lemma lem3932773 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3932774 (t1 : Prop) (t2 : Prop) : (term1091 t1 t2) = (term1092 t1 t2).
Proof. exact (MK_COMB (@lem3932773) (@lem3932772 t1 t2)). Qed.
Lemma lem3932775 (t1 : Prop) : (term1093 t1) = (term1094 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem3932774 t1 t2)). Qed.
Lemma lem3932776 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3932777 (t1 : Prop) : (term1095 t1) = (term1096 t1).
Proof. exact (MK_COMB (@lem3932776) (@lem3932775 t1)). Qed.
Lemma lem3932778 : term1097 = term1098.
Proof. exact (fun_ext (fun t1 : Prop => @lem3932777 t1)). Qed.
Lemma lem3932779 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3932780 : term1099 = term1100.
Proof. exact (MK_COMB (@lem3932779) (@lem3932778)). Qed.
Lemma lem3932781 : term1100.
Proof. exact (EQ_MP (@lem3932780) (@lem512)). Qed.
Lemma lem3932782 (t1 : Prop) : term1101 t1.
Proof. exact (@lem3932781 t1). Qed.
Lemma lem3932783 (t1 : Prop) : (term1101 t1) = (term1096 t1).
Proof. exact (eq_refl (term1101 t1)). Qed.
Lemma lem3932784 (t1 : Prop) : term1096 t1.
Proof. exact (EQ_MP (@lem3932783 t1) (@lem3932782 t1)). Qed.
Lemma lem3932785 (t1 : Prop) (t2 : Prop) : term1102 t1 t2.
Proof. exact (@lem3932784 t1 t2). Qed.
Lemma lem3932786 (t1 : Prop) (t2 : Prop) : (term1102 t1 t2) = (term1092 t1 t2).
Proof. exact (eq_refl (term1102 t1 t2)). Qed.
Lemma lem3932787 (t1 : Prop) (t2 : Prop) : term1092 t1 t2.
Proof. exact (EQ_MP (@lem3932786 t1 t2) (@lem3932785 t1 t2)). Qed.
Lemma lem3932788 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term1103 t1 t2 t3.
Proof. exact (@lem3932787 t1 t2 t3). Qed.
Lemma lem3932789 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1103 t1 t2 t3) = ((term1088 t1 t2 t3) = (term1087 t1 t2 t3)).
Proof. exact (eq_refl (term1103 t1 t2 t3)). Qed.
Lemma lem3932791 {_100044 : Type'} (s : _100044 -> Prop) : term1104 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3932792 {_100044 : Type'} (s : _100044 -> Prop) : (term1104 _100044 s) = (term1105 _100044 s).
Proof. exact (eq_refl (term1104 _100044 s)). Qed.
Lemma lem3932793 {_100044 : Type'} (s : _100044 -> Prop) : term1105 _100044 s.
Proof. exact (EQ_MP (@lem3932792 _100044 s) (@lem3932791 _100044 s)). Qed.
Lemma lem3932794 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term1106 _100044 s n.
Proof. exact (@lem3932793 _100044 s n). Qed.
Lemma lem3932795 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term1106 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term1107 _100044 s n)).
Proof. exact (eq_refl (term1106 _100044 s n)). Qed.
Lemma lem3932798 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term1107 _100044 s n).
Proof. exact (EQ_MP (@lem3932795 _100044 s n) (@lem3932794 _100044 s n)). Qed.
Lemma lem3932799 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term1107 A s n).
Proof. exact (@lem3932798 A s n). Qed.
Lemma lem3932800 {A : Type'} (s : A -> Prop) (m : nat) : (@HAS_SIZE A s m) = (term1107 A s m).
Proof. exact (@lem3932799 A s m). Qed.
Lemma lem3932801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3932802 {A : Type'} (s : A -> Prop) (m : nat) : (term1108 A s m) = (term1109 A s m).
Proof. exact (MK_COMB (@lem3932801) (@lem3932800 A s m)). Qed.
Lemma lem3932803 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1110 A B s t n) = (term1110 A B s t n).
Proof. exact (eq_refl (term1110 A B s t n)). Qed.
Lemma lem3932804 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1111 A B m s t n) = (term1112 A B m s t n).
Proof. exact (MK_COMB (@lem3932802 A s m) (@lem3932803 A B s t n)). Qed.
Lemma lem3932805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3932806 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1113 A B m s t n) = (term1114 A B m s t n).
Proof. exact (MK_COMB (@lem3932805) (@lem3932804 A B m s t n)). Qed.
Lemma lem3932807 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1115 A B s t m n) = (term1115 A B s t m n).
Proof. exact (eq_refl (term1115 A B s t m n)). Qed.
Lemma lem3932808 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1116 A B s t m n) = (term1117 A B s t m n).
Proof. exact (MK_COMB (@lem3932806 A B m s t n) (@lem3932807 A B s t m n)). Qed.
Lemma lem3932809 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1118 A B s t m) = (term1119 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem3932808 A B s t m n)). Qed.
Lemma lem3932810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932811 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1120 A B s t m) = (term1121 A B s t m).
Proof. exact (MK_COMB (@lem3932810) (@lem3932809 A B s t m)). Qed.
Lemma lem3932812 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1122 A B s t) = (term1123 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3932811 A B s t m)). Qed.
Lemma lem3932813 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932814 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1124 A B s t) = (term1125 A B s t).
Proof. exact (MK_COMB (@lem3932813) (@lem3932812 A B s t)). Qed.
Lemma lem3932815 {A B : Type'} (s : A -> Prop) : (term1126 A B s) = (term1127 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3932814 A B s t)). Qed.
Lemma lem3932816 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3932817 {A B : Type'} (s : A -> Prop) : (term1128 A B s) = (term1129 A B s).
Proof. exact (MK_COMB (@lem3932816 A B) (@lem3932815 A B s)). Qed.
Lemma lem3932818 {A B : Type'} : (term1130 A B) = (term1131 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3932817 A B s)). Qed.
Lemma lem3932819 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3932820 {A B : Type'} : (term1132 A B) = (term1133 A B).
Proof. exact (MK_COMB (@lem3932819 A) (@lem3932818 A B)). Qed.
Lemma lem3932821 {A B : Type'} : (term1133 A B) = (term1132 A B).
Proof. exact (SYM (@lem3932820 A B)). Qed.
Lemma lem3932841 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1088 t1 t2 t3) = (term1087 t1 t2 t3).
Proof. exact (EQ_MP (@lem3932789 t1 t2 t3) (@lem3932788 t1 t2 t3)). Qed.
Lemma lem3932842 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1112 A B m s t n) = (term1134 A B m s t n).
Proof. exact (@lem3932841 (@FINITE A s) ((@CARD A s) = m) (term1110 A B s t n)). Qed.
Lemma lem3932857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3932858 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1114 A B m s t n) = (term1135 A B m s t n).
Proof. exact (MK_COMB (@lem3932857) (@lem3932842 A B m s t n)). Qed.
Lemma lem3932863 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1115 A B s t m n) = (term1115 A B s t m n).
Proof. exact (eq_refl (term1115 A B s t m n)). Qed.
Lemma lem3932864 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1117 A B s t m n) = (term1136 A B s t m n).
Proof. exact (MK_COMB (@lem3932858 A B m s t n) (@lem3932863 A B s t m n)). Qed.
Lemma lem3932867 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1119 A B s t m) = (term1137 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem3932864 A B s t m n)). Qed.
Lemma lem3932868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932869 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1121 A B s t m) = (term1138 A B s t m).
Proof. exact (MK_COMB (@lem3932868) (@lem3932867 A B s t m)). Qed.
Lemma lem3932874 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1123 A B s t) = (term1139 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3932869 A B s t m)). Qed.
Lemma lem3932875 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932876 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1125 A B s t) = (term1140 A B s t).
Proof. exact (MK_COMB (@lem3932875) (@lem3932874 A B s t)). Qed.
Lemma lem3932881 {A B : Type'} (s : A -> Prop) : (term1127 A B s) = (term1141 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3932876 A B s t)). Qed.
Lemma lem3932882 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3932883 {A B : Type'} (s : A -> Prop) : (term1129 A B s) = (term1142 A B s).
Proof. exact (MK_COMB (@lem3932882 A B) (@lem3932881 A B s)). Qed.
Lemma lem3932888 {A B : Type'} : (term1131 A B) = (term1143 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3932883 A B s)). Qed.
Lemma lem3932889 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3932890 {A B : Type'} : (term1133 A B) = (term1144 A B).
Proof. exact (MK_COMB (@lem3932889 A) (@lem3932888 A B)). Qed.
Lemma lem3932895 {A B : Type'} : (term1144 A B) = (term1133 A B).
Proof. exact (SYM (@lem3932890 A B)). Qed.
Lemma lem3932913 (p : Prop) (q : Prop) (r : Prop) : (term1145 p q r) = (term1146 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3932914 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1136 A B s t m n) = (term1147 A B s t m n).
Proof. exact (@lem3932913 (@FINITE A s) (term1148 A B m s t n) (term1115 A B s t m n)). Qed.
Lemma lem3932915 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1137 A B s t m) = (term1149 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem3932914 A B s t m n)). Qed.
Lemma lem3932916 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932917 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1138 A B s t m) = (term1150 A B s t m).
Proof. exact (MK_COMB (@lem3932916) (@lem3932915 A B s t m)). Qed.
Lemma lem3932918 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1139 A B s t) = (term1151 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3932917 A B s t m)). Qed.
Lemma lem3932919 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932920 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1140 A B s t) = (term1152 A B s t).
Proof. exact (MK_COMB (@lem3932919) (@lem3932918 A B s t)). Qed.
Lemma lem3932921 {A B : Type'} (s : A -> Prop) : (term1141 A B s) = (term1153 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3932920 A B s t)). Qed.
Lemma lem3932922 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3932923 {A B : Type'} (s : A -> Prop) : (term1142 A B s) = (term1154 A B s).
Proof. exact (MK_COMB (@lem3932922 A B) (@lem3932921 A B s)). Qed.
Lemma lem3932924 {A B : Type'} : (term1143 A B) = (term1155 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3932923 A B s)). Qed.
Lemma lem3932925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3932926 {A B : Type'} : (term1144 A B) = (term1156 A B).
Proof. exact (MK_COMB (@lem3932925 A) (@lem3932924 A B)). Qed.
Lemma lem3932927 {A B : Type'} : (term1156 A B) = (term1144 A B).
Proof. exact (SYM (@lem3932926 A B)). Qed.
Lemma lem3932941 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1085 A P Q) = (term1086 A P Q).
Proof. exact (EQ_MP (@lem3932762 A P Q) (@lem3932761 A P Q)). Qed.
Lemma lem3932942 (P : Prop) (Q : nat -> Prop) : (term1157 P Q) = (term1158 P Q).
Proof. exact (@lem3932941 nat P Q). Qed.
Lemma lem3932943 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1159 A B s t m) = (term1160 A B s t m).
Proof. exact (@lem3932942 (@FINITE A s) (term1161 A B s t m)). Qed.
Lemma lem3932944 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1162 A B s t m n) = (term1163 A B s t m n).
Proof. exact (eq_refl (term1162 A B s t m n)). Qed.
Lemma lem3932945 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3932946 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1165 A B s t m n) = (term1147 A B s t m n).
Proof. exact (MK_COMB (@lem3932945 A s) (@lem3932944 A B s t m n)). Qed.
Lemma lem3932947 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1166 A B s t m) = (term1149 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem3932946 A B s t m n)). Qed.
Lemma lem3932948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932949 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1159 A B s t m) = (term1150 A B s t m).
Proof. exact (MK_COMB (@lem3932948) (@lem3932947 A B s t m)). Qed.
Lemma lem3932950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3932951 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1167 A B s t m) = (term1168 A B s t m).
Proof. exact (MK_COMB (@lem3932950) (@lem3932949 A B s t m)). Qed.
Lemma lem3932952 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1162 A B s t m n) = (term1163 A B s t m n).
Proof. exact (eq_refl (term1162 A B s t m n)). Qed.
Lemma lem3932953 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1169 A B s t m) = (term1161 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem3932952 A B s t m n)). Qed.
Lemma lem3932954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3932955 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1170 A B s t m) = (term1171 A B s t m).
Proof. exact (MK_COMB (@lem3932954) (@lem3932953 A B s t m)). Qed.
Lemma lem3932956 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3932957 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1160 A B s t m) = (term1172 A B s t m).
Proof. exact (MK_COMB (@lem3932956 A s) (@lem3932955 A B s t m)). Qed.
Lemma lem3932958 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : ((term1159 A B s t m) = (term1160 A B s t m)) = ((term1150 A B s t m) = (term1172 A B s t m)).
Proof. exact (MK_COMB (@lem3932951 A B s t m) (@lem3932957 A B s t m)). Qed.
Lemma lem3932959 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1150 A B s t m) = (term1172 A B s t m).
Proof. exact (EQ_MP (@lem3932958 A B s t m) (@lem3932943 A B s t m)). Qed.
Lemma lem3933024 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1151 A B s t) = (term1173 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3932959 A B s t m)). Qed.
Lemma lem3933025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3933026 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1152 A B s t) = (term1174 A B s t).
Proof. exact (MK_COMB (@lem3933025) (@lem3933024 A B s t)). Qed.
Lemma lem3933028 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1085 A P Q) = (term1086 A P Q).
Proof. exact (EQ_MP (@lem3932762 A P Q) (@lem3932761 A P Q)). Qed.
Lemma lem3933029 (P : Prop) (Q : nat -> Prop) : (term1157 P Q) = (term1158 P Q).
Proof. exact (@lem3933028 nat P Q). Qed.
Lemma lem3933030 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1175 A B s t) = (term1176 A B s t).
Proof. exact (@lem3933029 (@FINITE A s) (term1177 A B s t)). Qed.
Lemma lem3933031 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1178 A B s t m) = (term1171 A B s t m).
Proof. exact (eq_refl (term1178 A B s t m)). Qed.
Lemma lem3933032 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3933033 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1179 A B s t m) = (term1172 A B s t m).
Proof. exact (MK_COMB (@lem3933032 A s) (@lem3933031 A B s t m)). Qed.
Lemma lem3933034 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1180 A B s t) = (term1173 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3933033 A B s t m)). Qed.
Lemma lem3933035 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3933036 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1175 A B s t) = (term1174 A B s t).
Proof. exact (MK_COMB (@lem3933035) (@lem3933034 A B s t)). Qed.
Lemma lem3933037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3933038 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1181 A B s t) = (term1182 A B s t).
Proof. exact (MK_COMB (@lem3933037) (@lem3933036 A B s t)). Qed.
Lemma lem3933039 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1178 A B s t m) = (term1171 A B s t m).
Proof. exact (eq_refl (term1178 A B s t m)). Qed.
Lemma lem3933040 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1183 A B s t) = (term1177 A B s t).
Proof. exact (fun_ext (fun m : nat => @lem3933039 A B s t m)). Qed.
Lemma lem3933041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3933042 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1184 A B s t) = (term1185 A B s t).
Proof. exact (MK_COMB (@lem3933041) (@lem3933040 A B s t)). Qed.
Lemma lem3933043 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3933044 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1176 A B s t) = (term1186 A B s t).
Proof. exact (MK_COMB (@lem3933043 A s) (@lem3933042 A B s t)). Qed.
Lemma lem3933045 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : ((term1175 A B s t) = (term1176 A B s t)) = ((term1174 A B s t) = (term1186 A B s t)).
Proof. exact (MK_COMB (@lem3933038 A B s t) (@lem3933044 A B s t)). Qed.
Lemma lem3933046 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1174 A B s t) = (term1186 A B s t).
Proof. exact (EQ_MP (@lem3933045 A B s t) (@lem3933030 A B s t)). Qed.
Lemma lem3933115 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1152 A B s t) = (term1186 A B s t).
Proof. exact (TRANS (@lem3933026 A B s t) (@lem3933046 A B s t)). Qed.
Lemma lem3933116 {A B : Type'} (s : A -> Prop) : (term1153 A B s) = (term1187 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3933115 A B s t)). Qed.
Lemma lem3933117 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3933118 {A B : Type'} (s : A -> Prop) : (term1154 A B s) = (term1188 A B s).
Proof. exact (MK_COMB (@lem3933117 A B) (@lem3933116 A B s)). Qed.
Lemma lem3933120 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1085 A P Q) = (term1086 A P Q).
Proof. exact (EQ_MP (@lem3932762 A P Q) (@lem3932761 A P Q)). Qed.
Lemma lem3933121 {A B : Type'} (P : Prop) (Q : type475 A B) : (term1189 A B P Q) = (term1190 A B P Q).
Proof. exact (@lem3933120 (type1413 A B) P Q). Qed.
Lemma lem3933122 {A B : Type'} (s : A -> Prop) : (term1191 A B s) = (term1192 A B s).
Proof. exact (@lem3933121 A B (@FINITE A s) (term1193 A B s)). Qed.
Lemma lem3933123 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1194 A B s t) = (term1185 A B s t).
Proof. exact (eq_refl (term1194 A B s t)). Qed.
Lemma lem3933124 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3933125 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1195 A B s t) = (term1186 A B s t).
Proof. exact (MK_COMB (@lem3933124 A s) (@lem3933123 A B s t)). Qed.
Lemma lem3933126 {A B : Type'} (s : A -> Prop) : (term1196 A B s) = (term1187 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3933125 A B s t)). Qed.
Lemma lem3933127 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3933128 {A B : Type'} (s : A -> Prop) : (term1191 A B s) = (term1188 A B s).
Proof. exact (MK_COMB (@lem3933127 A B) (@lem3933126 A B s)). Qed.
Lemma lem3933129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3933130 {A B : Type'} (s : A -> Prop) : (term1197 A B s) = (term1198 A B s).
Proof. exact (MK_COMB (@lem3933129) (@lem3933128 A B s)). Qed.
Lemma lem3933131 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1194 A B s t) = (term1185 A B s t).
Proof. exact (eq_refl (term1194 A B s t)). Qed.
Lemma lem3933132 {A B : Type'} (s : A -> Prop) : (term1199 A B s) = (term1193 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3933131 A B s t)). Qed.
Lemma lem3933133 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3933134 {A B : Type'} (s : A -> Prop) : (term1200 A B s) = (term1201 A B s).
Proof. exact (MK_COMB (@lem3933133 A B) (@lem3933132 A B s)). Qed.
Lemma lem3933135 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3933136 {A B : Type'} (s : A -> Prop) : (term1192 A B s) = (term1202 A B s).
Proof. exact (MK_COMB (@lem3933135 A s) (@lem3933134 A B s)). Qed.
Lemma lem3933137 {A B : Type'} (s : A -> Prop) : ((term1191 A B s) = (term1192 A B s)) = ((term1188 A B s) = (term1202 A B s)).
Proof. exact (MK_COMB (@lem3933130 A B s) (@lem3933136 A B s)). Qed.
Lemma lem3933138 {A B : Type'} (s : A -> Prop) : (term1188 A B s) = (term1202 A B s).
Proof. exact (EQ_MP (@lem3933137 A B s) (@lem3933122 A B s)). Qed.
Lemma lem3933211 {A B : Type'} (s : A -> Prop) : (term1154 A B s) = (term1202 A B s).
Proof. exact (TRANS (@lem3933118 A B s) (@lem3933138 A B s)). Qed.
Lemma lem3933212 {A B : Type'} : (term1155 A B) = (term1203 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3933211 A B s)). Qed.
Lemma lem3933213 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3933214 {A B : Type'} : (term1156 A B) = (term1204 A B).
Proof. exact (MK_COMB (@lem3933213 A) (@lem3933212 A B)). Qed.
Lemma lem3933239 {A B : Type'} : (term1204 A B) = (term1156 A B).
Proof. exact (SYM (@lem3933214 A B)). Qed.
Lemma lem3933241 {A : Type'} (P : type686 A) : term1077 A P.
Proof. exact (EQ_MP (@lem3932756 A P) (@lem3932755 A P)). Qed.
Lemma lem3933242 {A : Type'} (P : type686 A) : term1077 A P.
Proof. exact (@lem3933241 A P). Qed.
Lemma lem3933243 {A B : Type'} : term1205 A B.
Proof. exact (@lem3933242 A (term1206 A B)). Qed.
Lemma lem3933244 {A B : Type'} : (term1207 A B) = (term1208 A B).
Proof. exact (eq_refl (term1207 A B)). Qed.
Lemma lem3933245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3933246 {A B : Type'} : (term1209 A B) = (term1210 A B).
Proof. exact (MK_COMB (@lem3933245) (@lem3933244 A B)). Qed.
Lemma lem3933247 {A B : Type'} (s : A -> Prop) : (term1211 A B s) = (term1201 A B s).
Proof. exact (eq_refl (term1211 A B s)). Qed.
Lemma lem3933248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3933249 {A B : Type'} (s : A -> Prop) : (term1212 A B s) = (term1213 A B s).
Proof. exact (MK_COMB (@lem3933248) (@lem3933247 A B s)). Qed.
Lemma lem3933250 {A : Type'} (x : A) (s : A -> Prop) : (term1214 A x s) = (term1214 A x s).
Proof. exact (eq_refl (term1214 A x s)). Qed.
Lemma lem3933251 {A B : Type'} (x : A) (s : A -> Prop) : (term1215 A B x s) = (term1216 A B x s).
Proof. exact (MK_COMB (@lem3933249 A B s) (@lem3933250 A x s)). Qed.
Lemma lem3933252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3933253 {A B : Type'} (x : A) (s : A -> Prop) : (term1217 A B x s) = (term1218 A B x s).
Proof. exact (MK_COMB (@lem3933252) (@lem3933251 A B x s)). Qed.
Lemma lem3933254 {A B : Type'} (x : A) (s : A -> Prop) : (term1219 A B x s) = (term1220 A B x s).
Proof. exact (eq_refl (term1219 A B x s)). Qed.
Lemma lem3933255 {A B : Type'} (x : A) (s : A -> Prop) : (term1221 A B x s) = (term1222 A B x s).
Proof. exact (MK_COMB (@lem3933253 A B x s) (@lem3933254 A B x s)). Qed.
Lemma lem3933256 {A B : Type'} (x : A) : (term1223 A B x) = (term1224 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3933255 A B x s)). Qed.
Lemma lem3933257 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3933258 {A B : Type'} (x : A) : (term1225 A B x) = (term1226 A B x).
Proof. exact (MK_COMB (@lem3933257 A) (@lem3933256 A B x)). Qed.
Lemma lem3933259 {A B : Type'} : (term1227 A B) = (term1228 A B).
Proof. exact (fun_ext (fun x : A => @lem3933258 A B x)). Qed.
Lemma lem3933260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3933261 {A B : Type'} : (term1229 A B) = (term1230 A B).
Proof. exact (MK_COMB (@lem3933260 A) (@lem3933259 A B)). Qed.
Lemma lem3933262 {A B : Type'} : (term1231 A B) = (term1232 A B).
Proof. exact (MK_COMB (@lem3933246 A B) (@lem3933261 A B)). Qed.
Lemma lem3933263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3933264 {A B : Type'} : (term1233 A B) = (term1234 A B).
Proof. exact (MK_COMB (@lem3933263) (@lem3933262 A B)). Qed.
Lemma lem3933265 {A B : Type'} (s : A -> Prop) : (term1211 A B s) = (term1201 A B s).
Proof. exact (eq_refl (term1211 A B s)). Qed.
Lemma lem3933266 {A : Type'} (s : A -> Prop) : (term1164 A s) = (term1164 A s).
Proof. exact (eq_refl (term1164 A s)). Qed.
Lemma lem3933267 {A B : Type'} (s : A -> Prop) : (term1235 A B s) = (term1202 A B s).
Proof. exact (MK_COMB (@lem3933266 A s) (@lem3933265 A B s)). Qed.
Lemma lem3933268 {A B : Type'} : (term1236 A B) = (term1203 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3933267 A B s)). Qed.
Lemma lem3933269 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3933270 {A B : Type'} : (term1237 A B) = (term1204 A B).
Proof. exact (MK_COMB (@lem3933269 A) (@lem3933268 A B)). Qed.
Lemma lem3933271 {A B : Type'} : (term1205 A B) = (term1238 A B).
Proof. exact (MK_COMB (@lem3933264 A B) (@lem3933270 A B)). Qed.
Lemma lem3933272 {A B : Type'} : term1238 A B.
Proof. exact (EQ_MP (@lem3933271 A B) (@lem3933243 A B)). Qed.
Lemma lem3933292 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3933293 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3933294 {A : Type'} : (term1239 A) = term1240.
Proof. exact (MK_COMB (@lem3933293) (@lem3933292 A)). Qed.
Lemma lem3933295 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem3933296 {A : Type'} (m : nat) : ((@CARD A (@EMPTY A)) = m) = ((NUMERAL 0) = m).
Proof. exact (MK_COMB (@lem3933294 A) (@lem3933295 m)). Qed.
Lemma lem3933299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3933300 {A : Type'} (m : nat) : (term1241 A m) = (term1242 m).
Proof. exact (MK_COMB (@lem3933299) (@lem3933296 A m)). Qed.
Lemma lem3933309 {A B : Type'} (t : type1413 A B) (n : nat) : (term1243 A B t n) = (term1243 A B t n).
Proof. exact (eq_refl (term1243 A B t n)). Qed.
Lemma lem3933310 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) : (term1244 A B m t n) = (term1245 A B m t n).
Proof. exact (MK_COMB (@lem3933300 A m) (@lem3933309 A B t n)). Qed.
Lemma lem3933313 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3933314 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) : (term1246 A B m t n) = (term1247 A B m t n).
Proof. exact (MK_COMB (@lem3933313) (@lem3933310 A B m t n)). Qed.
Lemma lem3933316 {_101250 _101251 : Type'} (t : type1413 _101250 _101251) : (term1025 _101250 _101251 t) = (@EMPTY _101251).
Proof. exact (EQ_MP (@lem3932590 _101250 _101251 t) (@lem3932725 _101250 _101251 t)). Qed.
Lemma lem3933317 {A B : Type'} (t : type1413 A B) : (term1025 A B t) = (@EMPTY B).
Proof. exact (@lem3933316 A B t). Qed.
Lemma lem3933318 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem3933319 {A B : Type'} (t : type1413 A B) : (term1248 A B t) = (@CARD B (@EMPTY B)).
Proof. exact (MK_COMB (@lem3933318 B) (@lem3933317 A B t)). Qed.
Lemma lem3933321 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3933322 {B : Type'} : (@CARD B (@EMPTY B)) = (NUMERAL 0).
Proof. exact (@lem3933321 B). Qed.
Lemma lem3933323 {A B : Type'} (t : type1413 A B) : (term1248 A B t) = (NUMERAL 0).
Proof. exact (TRANS (@lem3933319 A B t) (@lem3933322 B)). Qed.
Lemma lem3933324 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3933325 {A B : Type'} (t : type1413 A B) : (term1249 A B t) = term1250.
Proof. exact (MK_COMB (@lem3933324) (@lem3933323 A B t)). Qed.
Lemma lem3933326 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem3933327 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term1251 A B t m n) = (term1252 m n).
Proof. exact (MK_COMB (@lem3933325 A B t) (@lem3933326 m n)). Qed.
Lemma lem3933329 (n : nat) : (term1074 n) = True.
Proof. exact (EQ_MP (@lem3932730 n) (@lem3932729 n)). Qed.
Lemma lem3933330 (m : nat) (n : nat) : (term1252 m n) = True.
Proof. exact (@lem3933329 (Nat.mul m n)). Qed.
Lemma lem3933331 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term1251 A B t m n) = True.
Proof. exact (TRANS (@lem3933327 A B t m n) (@lem3933330 m n)). Qed.
Lemma lem3933332 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) : (term1253 A B t m n) = (term1254 A B m t n).
Proof. exact (MK_COMB (@lem3933314 A B m t n) (@lem3933331 A B t m n)). Qed.
Lemma lem3933334 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3933335 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) : (term1254 A B m t n) = True.
Proof. exact (@lem3933334 (term1245 A B m t n)). Qed.
Lemma lem3933336 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term1253 A B t m n) = True.
Proof. exact (TRANS (@lem3933332 A B m t n) (@lem3933335 A B m t n)). Qed.
Lemma lem3933337 {A B : Type'} (t : type1413 A B) (m : nat) : (term1255 A B t m) = term1256.
Proof. exact (fun_ext (fun n : nat => @lem3933336 A B t m n)). Qed.
Lemma lem3933338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3933339 {A B : Type'} (t : type1413 A B) (m : nat) : (term1257 A B t m) = term1258.
Proof. exact (MK_COMB (@lem3933338) (@lem3933337 A B t m)). Qed.
Lemma lem3933341 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3933342 (t : Prop) : (term1259 t) = t.
Proof. exact (@lem3933341 nat t). Qed.
Lemma lem3933343 : term1258 = True.
Proof. exact (@lem3933342 True). Qed.
Lemma lem3933344 {A B : Type'} (t : type1413 A B) (m : nat) : (term1257 A B t m) = True.
Proof. exact (TRANS (@lem3933339 A B t m) (@lem3933343)). Qed.
Lemma lem3933345 {A B : Type'} (t : type1413 A B) : (term1260 A B t) = term1256.
Proof. exact (fun_ext (fun m : nat => @lem3933344 A B t m)). Qed.
Lemma lem3933346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3933347 {A B : Type'} (t : type1413 A B) : (term1261 A B t) = term1258.
Proof. exact (MK_COMB (@lem3933346) (@lem3933345 A B t)). Qed.
Lemma lem3933349 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3933350 (t : Prop) : (term1259 t) = t.
Proof. exact (@lem3933349 nat t). Qed.
Lemma lem3933351 : term1258 = True.
Proof. exact (@lem3933350 True). Qed.
Lemma lem3933352 {A B : Type'} (t : type1413 A B) : (term1261 A B t) = True.
Proof. exact (TRANS (@lem3933347 A B t) (@lem3933351)). Qed.
Lemma lem3933353 {A B : Type'} : (term1262 A B) = (term1263 A B).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3933352 A B t)). Qed.
Lemma lem3933354 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3933355 {A B : Type'} : (term1208 A B) = (term1264 A B).
Proof. exact (MK_COMB (@lem3933354 A B) (@lem3933353 A B)). Qed.
Lemma lem3933357 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3933358 {A B : Type'} (t : Prop) : (term1265 A B t) = t.
Proof. exact (@lem3933357 (type1413 A B) t). Qed.
Lemma lem3933359 {A B : Type'} : (term1264 A B) = True.
Proof. exact (@lem3933358 A B True). Qed.
Lemma lem3933360 {A B : Type'} : (term1208 A B) = True.
Proof. exact (TRANS (@lem3933355 A B) (@lem3933359 A B)). Qed.
Lemma lem3933361 {A B : Type'} : True = (term1208 A B).
Proof. exact (SYM (@lem3933360 A B)). Qed.
Lemma lem3933362 {A B : Type'} : term1208 A B.
Proof. exact (EQ_MP (@lem3933361 A B) (@lem0)). Qed.
Lemma lem3933439 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1216 A B x s) : term1216 A B x s.
Proof. exact (h1). Qed.
Lemma lem3933440 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1214 A x s) : term1214 A x s.
Proof. exact (h1). Qed.
Lemma lem3933441 {A B : Type'} (s : A -> Prop) (h1 : term1201 A B s) : term1201 A B s.
Proof. exact (h1). Qed.
Lemma lem3933442 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3933443 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1266 A x s.
Proof. exact (h1). Qed.
Lemma lem3933463 {A : Type'} : term1267 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3933464 {A : Type'} (x : A) : term1268 A x.
Proof. exact (@lem3933463 A x). Qed.
Lemma lem3933465 {A : Type'} (x : A) : (term1268 A x) = (term1269 A x).
Proof. exact (eq_refl (term1268 A x)). Qed.
Lemma lem3933466 {A : Type'} (x : A) : term1269 A x.
Proof. exact (EQ_MP (@lem3933465 A x) (@lem3933464 A x)). Qed.
Lemma lem3933467 {A : Type'} (x : A) (s : A -> Prop) : term1270 A x s.
Proof. exact (@lem3933466 A x s). Qed.
Lemma lem3933468 {A : Type'} (x : A) (s : A -> Prop) : (term1270 A x s) = (term1271 A x s).
Proof. exact (eq_refl (term1270 A x s)). Qed.
Lemma lem3933469 {A : Type'} (x : A) (s : A -> Prop) : term1271 A x s.
Proof. exact (EQ_MP (@lem3933468 A x s) (@lem3933467 A x s)). Qed.
Lemma lem3933470 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3933471 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term1272 A x s) = (term1273 A x s).
Proof. exact (@lem3933469 A x s (@lem3933470 A s h1)). Qed.
Lemma lem3933496 {A : Type'} (x : A) (s : A -> Prop) : term1274 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3933498 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3933503 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1275 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3933504 (p : Prop) (q : Prop) (p' : Prop) : term1276 p q p'.
Proof. exact (fun q' : Prop => @lem3933503 p q p' q'). Qed.
Lemma lem3933505 (p : Prop) (q : Prop) : term1277 p q.
Proof. exact (fun p' : Prop => @lem3933504 p q p'). Qed.
Lemma lem3933506 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term1278 A B x s t m n.
Proof. exact (@lem3933505 (term1279 A B m x s t n) (term1280 A B x s t m n)). Qed.
Lemma lem3933507 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term1281 A B x s t m n p'.
Proof. exact (@lem3933506 A B x s t m n p'). Qed.
Lemma lem3933508 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : (term1281 A B x s t m n p') = (term1282 A B x s t m n p').
Proof. exact (eq_refl (term1281 A B x s t m n p')). Qed.
Lemma lem3933509 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term1282 A B x s t m n p'.
Proof. exact (EQ_MP (@lem3933508 A B x s t m n p') (@lem3933507 A B x s t m n p')). Qed.
Lemma lem3933510 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term1283 A B x s t m n p' q'.
Proof. exact (@lem3933509 A B x s t m n p' q'). Qed.
Lemma lem3933511 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term1283 A B x s t m n p' q') = (term1284 A B x s t m n p' q').
Proof. exact (eq_refl (term1283 A B x s t m n p' q')). Qed.
Lemma lem3933512 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term1284 A B x s t m n p' q'.
Proof. exact (EQ_MP (@lem3933511 A B x s t m n p' q') (@lem3933510 A B x s t m n p' q')). Qed.
Lemma lem3933518 {A : Type'} (x : A) (s : A -> Prop) : term1271 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3933471 A x s h0). Qed.
Lemma lem3933519 {A : Type'} (x : A) (s : A -> Prop) : term1271 A x s.
Proof. exact (@lem3933518 A x s). Qed.
Lemma lem3933521 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3933498 A s) (@lem3933442 A s h1)). Qed.
Lemma lem3933522 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3933521 A s h1)). Qed.
Lemma lem3933523 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3933522 A s h1) (@lem0)). Qed.
Lemma lem3933524 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term1272 A x s) = (term1273 A x s).
Proof. exact (@lem3933519 A x s (@lem3933523 A s h1)). Qed.
Lemma lem3933526 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term1285 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3933527 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term1286 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3933526 _2963 g t e g' t' e'). Qed.
Lemma lem3933528 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term1287 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3933527 _2963 g t e g' t'). Qed.
Lemma lem3933529 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term1288 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3933528 _2963 g t e g'). Qed.
Lemma lem3933530 (g : Prop) (t : nat) (e : nat) : term1289 g t e.
Proof. exact (@lem3933529 nat g t e). Qed.
Lemma lem3933531 {A : Type'} (x : A) (s : A -> Prop) : term1290 A x s.
Proof. exact (@lem3933530 (@IN A x s) (@CARD A s) (term1291 A s)). Qed.
Lemma lem3933532 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term1292 A x s g'.
Proof. exact (@lem3933531 A x s g'). Qed.
Lemma lem3933533 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term1292 A x s g') = (term1293 A x s g').
Proof. exact (eq_refl (term1292 A x s g')). Qed.
Lemma lem3933534 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term1293 A x s g'.
Proof. exact (EQ_MP (@lem3933533 A x s g') (@lem3933532 A x s g')). Qed.
Lemma lem3933535 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term1294 A x s g' t'.
Proof. exact (@lem3933534 A x s g' t'). Qed.
Lemma lem3933536 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term1294 A x s g' t') = (term1295 A x s g' t').
Proof. exact (eq_refl (term1294 A x s g' t')). Qed.
Lemma lem3933537 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term1295 A x s g' t'.
Proof. exact (EQ_MP (@lem3933536 A x s g' t') (@lem3933535 A x s g' t')). Qed.
Lemma lem3933538 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1296 A x s g' t' e'.
Proof. exact (@lem3933537 A x s g' t' e'). Qed.
Lemma lem3933539 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term1296 A x s g' t' e') = (term1297 A x s g' t' e').
Proof. exact (eq_refl (term1296 A x s g' t' e')). Qed.
Lemma lem3933540 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1297 A x s g' t' e'.
Proof. exact (EQ_MP (@lem3933539 A x s g' t' e') (@lem3933538 A x s g' t' e')). Qed.
Lemma lem3933542 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (@IN A x s) = False.
Proof. exact (@lem3933496 A x s (@lem3933443 A x s h1)). Qed.
Lemma lem3933543 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term1298 A x s t' e'.
Proof. exact (@lem3933540 A x s False t' e'). Qed.
Lemma lem3933544 {A : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1299 A x s t' e'.
Proof. exact (@lem3933543 A x s t' e' (@lem3933542 A x s h1)). Qed.
Lemma lem3933548 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3933549 {A : Type'} (s : A -> Prop) : term1300 A s.
Proof. exact (fun h0 : False => @lem3933548 A s). Qed.
Lemma lem3933550 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1301 A x s e'.
Proof. exact (@lem3933544 A (@CARD A s) e' x s h1). Qed.
Lemma lem3933551 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1302 A x s e'.
Proof. exact (@lem3933550 A e' x s h1 (@lem3933549 A s)). Qed.
Lemma lem3933557 {A : Type'} (s : A -> Prop) : (term1291 A s) = (term1291 A s).
Proof. exact (eq_refl (term1291 A s)). Qed.
Lemma lem3933558 {A : Type'} (s : A -> Prop) : term1303 A s.
Proof. exact (fun h0 : ~ False => @lem3933557 A s). Qed.
Lemma lem3933559 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1304 A x s.
Proof. exact (@lem3933551 A (term1291 A s) x s h1). Qed.
Lemma lem3933560 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1273 A x s) = (term1305 A s).
Proof. exact (@lem3933559 A x s h1 (@lem3933558 A s)). Qed.
Lemma lem3933562 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3933563 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3933562 nat t1 t2). Qed.
Lemma lem3933564 {A : Type'} (s : A -> Prop) : (term1305 A s) = (term1291 A s).
Proof. exact (@lem3933563 (@CARD A s) (term1291 A s)). Qed.
Lemma lem3933565 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1273 A x s) = (term1291 A s).
Proof. exact (TRANS (@lem3933560 A x s h1) (@lem3933564 A s)). Qed.
Lemma lem3933566 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1272 A x s) = (term1291 A s).
Proof. exact (TRANS (@lem3933524 A x s h1) (@lem3933565 A x s h2)). Qed.
Lemma lem3933567 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3933568 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1306 A x s) = (term1307 A s).
Proof. exact (MK_COMB (@lem3933567) (@lem3933566 A x s h1 h2)). Qed.
Lemma lem3933569 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem3933570 {A : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : ((term1272 A x s) = m) = ((term1291 A s) = m).
Proof. exact (MK_COMB (@lem3933568 A x s h1 h2) (@lem3933569 m)). Qed.
Lemma lem3933573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3933574 {A : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1308 A x s m) = (term1309 A s m).
Proof. exact (MK_COMB (@lem3933573) (@lem3933570 A m x s h1 h2)). Qed.
Lemma lem3933608 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1310 A B x s t n) = (term1310 A B x s t n).
Proof. exact (eq_refl (term1310 A B x s t n)). Qed.
Lemma lem3933609 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1279 A B m x s t n) = (term1311 A B m x s t n).
Proof. exact (MK_COMB (@lem3933574 A m x s h1 h2) (@lem3933608 A B x s t n)). Qed.
Lemma lem3933645 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (q' : Prop) : term1312 A B m x s t n q'.
Proof. exact (@lem3933512 A B x s t m n (term1311 A B m x s t n) q'). Qed.
Lemma lem3933646 {A B : Type'} (m : nat) (t : type1413 A B) (n : nat) (q' : Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : term1313 A B m x s t n q'.
Proof. exact (@lem3933645 A B m x s t n q' (@lem3933609 A B m t n x s h1 h2)). Qed.
Lemma lem3933675 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1280 A B x s t m n) = (term1280 A B x s t m n).
Proof. exact (eq_refl (term1280 A B x s t m n)). Qed.
Lemma lem3933676 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term1314 A B x s t m n.
Proof. exact (fun h0 : term1311 A B m x s t n => @lem3933675 A B x s t m n). Qed.
Lemma lem3933677 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : term1315 A B x s t m n.
Proof. exact (@lem3933646 A B m t n (term1280 A B x s t m n) x s h1 h2). Qed.
Lemma lem3933678 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1316 A B x s t m n) = (term1317 A B x s t m n).
Proof. exact (@lem3933677 A B t m n x s h1 h2 (@lem3933676 A B x s t m n)). Qed.
Lemma lem3933801 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term1266 A x s) : (term1317 A B x s t m n) = (term1316 A B x s t m n).
Proof. exact (SYM (@lem3933678 A B t m n x s h1 h2)). Qed.
Lemma lem3933802 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1311 A B m x s t n) : term1311 A B m x s t n.
Proof. exact (h1). Qed.
Lemma lem3933803 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1310 A B x s t n.
Proof. exact (h1). Qed.
Lemma lem3933804 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term1291 A s) = m) : (term1291 A s) = m.
Proof. exact (h1). Qed.
Lemma lem3933805 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term1291 A s) = m) : m = (term1291 A s).
Proof. exact (SYM (@lem3933804 A s m h1)). Qed.
Lemma lem3933806 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1318 A B x s t n) = (term1318 A B x s t n).
Proof. exact (eq_refl (term1318 A B x s t n)). Qed.
Lemma lem3933807 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term1291 A s) = m) : (term1319 A B x s t n m) = (term1320 A B x t n s).
Proof. exact (MK_COMB (@lem3933806 A B x s t n) (@lem3933805 A s m h1)). Qed.
Lemma lem3933808 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1320 A B x t n s) = (term1321 A B x t s n).
Proof. exact (eq_refl (term1320 A B x t n s)). Qed.
Lemma lem3933809 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (m : nat) : (term1322 A B x s t n m) = (term1322 A B x s t n m).
Proof. exact (eq_refl (term1322 A B x s t n m)). Qed.
Lemma lem3933810 {A B : Type'} (m : nat) (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : ((term1319 A B x s t n m) = (term1320 A B x t n s)) = ((term1319 A B x s t n m) = (term1321 A B x t s n)).
Proof. exact (MK_COMB (@lem3933809 A B x s t n m) (@lem3933808 A B x t s n)). Qed.
Lemma lem3933811 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1319 A B x s t n m) = (term1280 A B x s t m n).
Proof. exact (eq_refl (term1319 A B x s t n m)). Qed.
Lemma lem3933812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3933813 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1322 A B x s t n m) = (term1323 A B x s t m n).
Proof. exact (MK_COMB (@lem3933812) (@lem3933811 A B x s t m n)). Qed.
Lemma lem3933814 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1321 A B x t s n) = (term1321 A B x t s n).
Proof. exact (eq_refl (term1321 A B x t s n)). Qed.
Lemma lem3933815 {A B : Type'} (m : nat) (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : ((term1319 A B x s t n m) = (term1321 A B x t s n)) = ((term1280 A B x s t m n) = (term1321 A B x t s n)).
Proof. exact (MK_COMB (@lem3933813 A B x s t m n) (@lem3933814 A B x t s n)). Qed.
Lemma lem3933816 {A B : Type'} (m : nat) (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : ((term1319 A B x s t n m) = (term1320 A B x t n s)) = ((term1280 A B x s t m n) = (term1321 A B x t s n)).
Proof. exact (TRANS (@lem3933810 A B m x t s n) (@lem3933815 A B m x t s n)). Qed.
Lemma lem3933817 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term1291 A s) = m) : (term1280 A B x s t m n) = (term1321 A B x t s n).
Proof. exact (EQ_MP (@lem3933816 A B m x t s n) (@lem3933807 A B x t n s m h1)). Qed.
Lemma lem3933818 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term1291 A s) = m) : (term1321 A B x t s n) = (term1280 A B x s t m n).
Proof. exact (SYM (@lem3933817 A B x t n s m h1)). Qed.
Lemma lem3933832 {A B : Type'} (s : A -> Prop) (h1 : term1201 A B s) : term1201 A B s.
Proof. exact (h1). Qed.
Lemma lem3933846 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1266 A x s.
Proof. exact (h1). Qed.
Lemma lem3933860 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3933862 {_101211 _101227 : Type'} (a : _101227) (s : _101227 -> Prop) (t : type1470 _101211 _101227) : (term523 _101211 _101227 a s t) = (term524 _101211 _101227 a s t).
Proof. exact (EQ_MP (@lem3929750 _101211 _101227 a s t) (@lem3932560 _101211 _101227 a s t)). Qed.
Lemma lem3933863 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term1324 A B a s t) = (term1325 A B a s t).
Proof. exact (@lem3933862 B A a s t). Qed.
Lemma lem3933864 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1324 A B x s t) = (term1325 A B x s t).
Proof. exact (@lem3933863 A B x s t). Qed.
Lemma lem3933869 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem3933870 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1326 A B x s t) = (term1327 A B x s t).
Proof. exact (MK_COMB (@lem3933869 B) (@lem3933864 A B x s t)). Qed.
Lemma lem3933871 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem3933872 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1328 A B x s t) = (term1329 A B x s t).
Proof. exact (MK_COMB (@lem3933871) (@lem3933870 A B x s t)). Qed.
Lemma lem3933873 {A : Type'} (s : A -> Prop) (n : nat) : (term1330 A s n) = (term1330 A s n).
Proof. exact (eq_refl (term1330 A s n)). Qed.
Lemma lem3933874 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1321 A B x t s n) = (term1331 A B x t s n).
Proof. exact (MK_COMB (@lem3933872 A B x s t) (@lem3933873 A s n)). Qed.
Lemma lem3933875 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1331 A B x t s n) = (term1321 A B x t s n).
Proof. exact (SYM (@lem3933874 A B x t s n)). Qed.
Lemma lem3933877 (m : nat) (p : nat) : term510 m p.
Proof. exact (EQ_MP (@lem3929716 m p) (@lem3929715 m p)). Qed.
Lemma lem3933878 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : term1332 A B x t s n.
Proof. exact (@lem3933877 (term1327 A B x s t) (term1330 A s n)). Qed.
Lemma lem3933880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term494 A s t.
Proof. exact (EQ_MP (@lem3929688 A s t) (@lem3929687 A s t)). Qed.
Lemma lem3933881 {B : Type'} (s : B -> Prop) (t : B -> Prop) : term494 B s t.
Proof. exact (@lem3933880 B s t). Qed.
Lemma lem3933882 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : term1333 A B x s t.
Proof. exact (@lem3933881 B (t x) (term1334 A B s t)). Qed.
Lemma lem3933885 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1335 A B x s t) = (term1335 A B x s t).
Proof. exact (eq_refl (term1335 A B x s t)). Qed.
Lemma lem3933886 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1335 A B x s t) = (term1333 A B x s t).
Proof. exact (eq_refl (term1335 A B x s t)). Qed.
Lemma lem3933887 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1336 A B x s t) = (term1336 A B x s t).
Proof. exact (eq_refl (term1336 A B x s t)). Qed.
Lemma lem3933888 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term1335 A B x s t) = (term1335 A B x s t)) = ((term1335 A B x s t) = (term1333 A B x s t)).
Proof. exact (MK_COMB (@lem3933887 A B x s t) (@lem3933886 A B x s t)). Qed.
Lemma lem3933889 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1335 A B x s t) = (term1333 A B x s t).
Proof. exact (eq_refl (term1335 A B x s t)). Qed.
Lemma lem3933890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3933891 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1336 A B x s t) = (term1337 A B x s t).
Proof. exact (MK_COMB (@lem3933890) (@lem3933889 A B x s t)). Qed.
Lemma lem3933892 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1333 A B x s t) = (term1333 A B x s t).
Proof. exact (eq_refl (term1333 A B x s t)). Qed.
Lemma lem3933893 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term1335 A B x s t) = (term1333 A B x s t)) = ((term1333 A B x s t) = (term1333 A B x s t)).
Proof. exact (MK_COMB (@lem3933891 A B x s t) (@lem3933892 A B x s t)). Qed.
Lemma lem3933894 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term1335 A B x s t) = (term1335 A B x s t)) = ((term1333 A B x s t) = (term1333 A B x s t)).
Proof. exact (TRANS (@lem3933888 A B x s t) (@lem3933893 A B x s t)). Qed.
Lemma lem3933895 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1333 A B x s t) = (term1333 A B x s t).
Proof. exact (EQ_MP (@lem3933894 A B x s t) (@lem3933885 A B x s t)). Qed.
Lemma lem3933896 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : term1333 A B x s t.
Proof. exact (EQ_MP (@lem3933895 A B x s t) (@lem3933882 A B x s t)). Qed.
Lemma lem3933897 {A : Type'} (x : A) : term1338 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3933898 {A : Type'} (x : A) : (term1338 A x) = (term1339 A x).
Proof. exact (eq_refl (term1338 A x)). Qed.
Lemma lem3933899 {A : Type'} (x : A) : term1339 A x.
Proof. exact (EQ_MP (@lem3933898 A x) (@lem3933897 A x)). Qed.
Lemma lem3933900 {A : Type'} (x : A) (y : A) : term1340 A x y.
Proof. exact (@lem3933899 A x y). Qed.
Lemma lem3933901 {A : Type'} (y : A) (x : A) : (term1340 A x y) = (term1341 A y x).
Proof. exact (eq_refl (term1340 A x y)). Qed.
Lemma lem3933902 {A : Type'} (y : A) (x : A) : term1341 A y x.
Proof. exact (EQ_MP (@lem3933901 A y x) (@lem3933900 A x y)). Qed.
Lemma lem3933903 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term1342 A y x s.
Proof. exact (@lem3933902 A y x s). Qed.
Lemma lem3933904 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term1342 A y x s) = ((term549 A x y s) = (term556 A y x s)).
Proof. exact (eq_refl (term1342 A y x s)). Qed.
Lemma lem3933924 {A : Type'} (x : A) (s : A -> Prop) : term1274 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3933928 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1343 A B x s t n x'.
Proof. exact (@lem3933803 A B x s t n h1 x'). Qed.
Lemma lem3933929 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term1343 A B x s t n x') = (term1344 A B x s t x' n).
Proof. exact (eq_refl (term1343 A B x s t n x')). Qed.
Lemma lem3933930 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1344 A B x s t x' n.
Proof. exact (EQ_MP (@lem3933929 A B x s t x' n) (@lem3933928 A B x' x s t n h1)). Qed.
Lemma lem3933931 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term549 A x' x s) : term549 A x' x s.
Proof. exact (h1). Qed.
Lemma lem3933932 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1345 A B t x' n.
Proof. exact (@lem3933930 A B x' x s t n h1 (@lem3933931 A x' x s h2)). Qed.
Lemma lem3933941 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1346 A B t x'.
Proof. exact (proj1 (@lem3933932 A B t n x' x s h1 h2)). Qed.
Lemma lem3933942 {A B : Type'} (t : type1413 A B) (x' : A) : (term1346 A B t x') = ((term1346 A B t x') = True).
Proof. exact (@lem7 (term1346 A B t x')). Qed.
Lemma lem3933943 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : (term1346 A B t x') = True.
Proof. exact (EQ_MP (@lem3933942 A B t x') (@lem3933941 A B t n x' x s h1 h2)). Qed.
Lemma lem3933952 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (fun h0 : term549 A x' x s => @lem3933943 A B t n x' x s h1 h0). Qed.
Lemma lem3933953 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (@lem3933952 A B x' x s t n h1). Qed.
Lemma lem3933954 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1348 A B s t x.
Proof. exact (@lem3933953 A B x x s t n h1). Qed.
Lemma lem3933956 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3933904 A y x s) (@lem3933903 A y x s)). Qed.
Lemma lem3933957 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (@lem3933956 A y x s). Qed.
Lemma lem3933958 {A : Type'} (x : A) (s : A -> Prop) : (term1349 A x s) = (term1350 A x s).
Proof. exact (@lem3933957 A x x s). Qed.
Lemma lem3933962 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3933963 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3933962 A x). Qed.
Lemma lem3933964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3933965 {A : Type'} (x : A) : (term1351 A x) = (or True).
Proof. exact (MK_COMB (@lem3933964) (@lem3933963 A x)). Qed.
Lemma lem3933967 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (@IN A x s) = False.
Proof. exact (@lem3933924 A x s (@lem3933846 A x s h1)). Qed.
Lemma lem3933968 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1350 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem3933965 A x) (@lem3933967 A x s h1)). Qed.
Lemma lem3933970 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3933971 : (True \/ False) = True.
Proof. exact (@lem3933970 False). Qed.
Lemma lem3933972 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1350 A x s) = True.
Proof. exact (TRANS (@lem3933968 A x s h1) (@lem3933971)). Qed.
Lemma lem3933973 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1349 A x s) = True.
Proof. exact (TRANS (@lem3933958 A x s) (@lem3933972 A x s h1)). Qed.
Lemma lem3933974 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : True = (term1349 A x s).
Proof. exact (SYM (@lem3933973 A x s h1)). Qed.
Lemma lem3933975 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1349 A x s.
Proof. exact (EQ_MP (@lem3933974 A x s h1) (@lem0)). Qed.
Lemma lem3933976 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1346 A B t x) = True.
Proof. exact (@lem3933954 A B x s t n h1 (@lem3933975 A x s h2)). Qed.
Lemma lem3933977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3933978 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1352 A B t x) = (and True).
Proof. exact (MK_COMB (@lem3933977) (@lem3933976 A B t n x s h1 h2)). Qed.
Lemma lem3933983 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1353 A B s t) = (term1353 A B s t).
Proof. exact (eq_refl (term1353 A B s t)). Qed.
Lemma lem3933984 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1354 A B x s t) = (term1355 A B s t).
Proof. exact (MK_COMB (@lem3933978 A B t n x s h1 h2) (@lem3933983 A B s t)). Qed.
Lemma lem3933986 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3933987 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1355 A B s t) = (term1353 A B s t).
Proof. exact (@lem3933986 (term1353 A B s t)). Qed.
Lemma lem3933992 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1354 A B x s t) = (term1353 A B s t).
Proof. exact (TRANS (@lem3933984 A B t n x s h1 h2) (@lem3933987 A B s t)). Qed.
Lemma lem3933993 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1353 A B s t) = (term1354 A B x s t).
Proof. exact (SYM (@lem3933992 A B t n x s h1 h2)). Qed.
Lemma lem3933995 {_101149 _101153 : Type'} (t : _101149 -> _101153) (s : _101149 -> Prop) : (term301 _101149 _101153 s t) = (@IMAGE _101149 _101153 t s).
Proof. exact (EQ_MP (@lem3928652 _101149 _101153 t s) (@lem3929665 _101149 _101153 t s)). Qed.
Lemma lem3933996 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term1356 A B s t) = (@IMAGE A (B -> Prop) t s).
Proof. exact (@lem3933995 A (B -> Prop) t s). Qed.
Lemma lem3933997 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem3933998 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term1334 A B s t) = (term1357 A B t s).
Proof. exact (MK_COMB (@lem3933997 B) (@lem3933996 A B t s)). Qed.
Lemma lem3933999 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem3934000 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term1353 A B s t) = (term1358 A B t s).
Proof. exact (MK_COMB (@lem3933999 B) (@lem3933998 A B t s)). Qed.
Lemma lem3934001 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1358 A B t s) = (term1353 A B s t).
Proof. exact (SYM (@lem3934000 A B t s)). Qed.
Lemma lem3934002 {A : Type'} (x : A) : term1338 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3934003 {A : Type'} (x : A) : (term1338 A x) = (term1339 A x).
Proof. exact (eq_refl (term1338 A x)). Qed.
Lemma lem3934004 {A : Type'} (x : A) : term1339 A x.
Proof. exact (EQ_MP (@lem3934003 A x) (@lem3934002 A x)). Qed.
Lemma lem3934005 {A : Type'} (x : A) (y : A) : term1340 A x y.
Proof. exact (@lem3934004 A x y). Qed.
Lemma lem3934006 {A : Type'} (y : A) (x : A) : (term1340 A x y) = (term1341 A y x).
Proof. exact (eq_refl (term1340 A x y)). Qed.
Lemma lem3934007 {A : Type'} (y : A) (x : A) : term1341 A y x.
Proof. exact (EQ_MP (@lem3934006 A y x) (@lem3934005 A x y)). Qed.
Lemma lem3934008 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term1342 A y x s.
Proof. exact (@lem3934007 A y x s). Qed.
Lemma lem3934009 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term1342 A y x s) = ((term549 A x y s) = (term556 A y x s)).
Proof. exact (eq_refl (term1342 A y x s)). Qed.
Lemma lem3934011 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term1359 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem3934012 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term1359 _87967 _87968 P f) = (term1360 _87967 _87968 P f).
Proof. exact (eq_refl (term1359 _87967 _87968 P f)). Qed.
Lemma lem3934013 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term1360 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem3934012 _87967 _87968 P f) (@lem3934011 _87967 _87968 P f)). Qed.
Lemma lem3934014 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term1361 _87967 _87968 P f s.
Proof. exact (@lem3934013 _87967 _87968 P f s). Qed.
Lemma lem3934015 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term1361 _87967 _87968 P f s) = ((term1362 _87967 _87968 f s P) = (term1363 _87967 _87968 s P f)).
Proof. exact (eq_refl (term1361 _87967 _87968 P f s)). Qed.
Lemma lem3934017 {A B : Type'} (f : A -> B) : term1364 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3934018 {A B : Type'} (f : A -> B) : (term1364 A B f) = (term1365 A B f).
Proof. exact (eq_refl (term1364 A B f)). Qed.
Lemma lem3934019 {A B : Type'} (f : A -> B) : term1365 A B f.
Proof. exact (EQ_MP (@lem3934018 A B f) (@lem3934017 A B f)). Qed.
Lemma lem3934020 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1366 A B f s.
Proof. exact (@lem3934019 A B f s). Qed.
Lemma lem3934021 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1366 A B f s) = (term1367 A B f s).
Proof. exact (eq_refl (term1366 A B f s)). Qed.
Lemma lem3934022 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1367 A B f s.
Proof. exact (EQ_MP (@lem3934021 A B f s) (@lem3934020 A B f s)). Qed.
Lemma lem3934023 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3934024 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term1368 A B f s.
Proof. exact (@lem3934022 A B f s (@lem3934023 A s h1)). Qed.
Lemma lem3934025 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1368 A B f s) = ((term1368 A B f s) = True).
Proof. exact (@lem7 (term1368 A B f s)). Qed.
Lemma lem3934026 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term1368 A B f s) = True.
Proof. exact (EQ_MP (@lem3934025 A B f s) (@lem3934024 A B f s h1)). Qed.
Lemma lem3934032 {_92445 : Type'} (s : type686 _92445) : term1369 _92445 s.
Proof. exact (@lem3612894 _92445 s). Qed.
Lemma lem3934033 {_92445 : Type'} (s : type686 _92445) : (term1369 _92445 s) = (term1370 _92445 s).
Proof. exact (eq_refl (term1369 _92445 s)). Qed.
Lemma lem3934034 {_92445 : Type'} (s : type686 _92445) : term1370 _92445 s.
Proof. exact (EQ_MP (@lem3934033 _92445 s) (@lem3934032 _92445 s)). Qed.
Lemma lem3934035 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : @FINITE (_92445 -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem3934036 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : (term1371 _92445 s) = (term1372 _92445 s).
Proof. exact (@lem3934034 _92445 s (@lem3934035 _92445 s h1)). Qed.
Lemma lem3934062 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3934064 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1343 A B x s t n x'.
Proof. exact (@lem3933803 A B x s t n h1 x'). Qed.
Lemma lem3934065 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term1343 A B x s t n x') = (term1344 A B x s t x' n).
Proof. exact (eq_refl (term1343 A B x s t n x')). Qed.
Lemma lem3934066 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1344 A B x s t x' n.
Proof. exact (EQ_MP (@lem3934065 A B x s t x' n) (@lem3934064 A B x' x s t n h1)). Qed.
Lemma lem3934067 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term549 A x' x s) : term549 A x' x s.
Proof. exact (h1). Qed.
Lemma lem3934068 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1345 A B t x' n.
Proof. exact (@lem3934066 A B x' x s t n h1 (@lem3934067 A x' x s h2)). Qed.
Lemma lem3934077 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1346 A B t x'.
Proof. exact (proj1 (@lem3934068 A B t n x' x s h1 h2)). Qed.
Lemma lem3934078 {A B : Type'} (t : type1413 A B) (x' : A) : (term1346 A B t x') = ((term1346 A B t x') = True).
Proof. exact (@lem7 (term1346 A B t x')). Qed.
Lemma lem3934079 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : (term1346 A B t x') = True.
Proof. exact (EQ_MP (@lem3934078 A B t x') (@lem3934077 A B t n x' x s h1 h2)). Qed.
Lemma lem3934086 {_92445 : Type'} (s : type686 _92445) : term1370 _92445 s.
Proof. exact (fun h0 : @FINITE (_92445 -> Prop) s => @lem3934036 _92445 s h0). Qed.
Lemma lem3934087 {B : Type'} (s : type686 B) : term1370 B s.
Proof. exact (@lem3934086 B s). Qed.
Lemma lem3934088 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : term1373 A B t s.
Proof. exact (@lem3934087 B (@IMAGE A (B -> Prop) t s)). Qed.
Lemma lem3934090 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1374 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3934026 A B f s h0). Qed.
Lemma lem3934091 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : term1375 A B f s.
Proof. exact (@lem3934090 A (B -> Prop) f s). Qed.
Lemma lem3934092 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : term1375 A B t s.
Proof. exact (@lem3934091 A B t s). Qed.
Lemma lem3934094 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3934062 A s) (@lem3933860 A s h1)). Qed.
Lemma lem3934095 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3934094 A s h1)). Qed.
Lemma lem3934096 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3934095 A s h1) (@lem0)). Qed.
Lemma lem3934097 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : (term1376 A B t s) = True.
Proof. exact (@lem3934092 A B t s (@lem3934096 A s h1)). Qed.
Lemma lem3934098 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : True = (term1376 A B t s).
Proof. exact (SYM (@lem3934097 A B t s h1)). Qed.
Lemma lem3934099 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : term1376 A B t s.
Proof. exact (EQ_MP (@lem3934098 A B t s h1) (@lem0)). Qed.
Lemma lem3934100 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : (term1358 A B t s) = (term1377 A B t s).
Proof. exact (@lem3934088 A B t s (@lem3934099 A B t s h1)). Qed.
Lemma lem3934102 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term1362 _87967 _87968 f s P) = (term1363 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3934015 _87967 _87968 s P f) (@lem3934014 _87967 _87968 P f s)). Qed.
Lemma lem3934103 {A B : Type'} (s : A -> Prop) (P : type686 B) (f : type1413 A B) : (term1378 A B f s P) = (term1379 A B s P f).
Proof. exact (@lem3934102 (B -> Prop) A s P f). Qed.
Lemma lem3934104 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1377 A B t s) = (term1380 A B s t).
Proof. exact (@lem3934103 A B s (@FINITE B) t). Qed.
Lemma lem3934168 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1275 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3934169 (p : Prop) (q : Prop) (p' : Prop) : term1276 p q p'.
Proof. exact (fun q' : Prop => @lem3934168 p q p' q'). Qed.
Lemma lem3934170 (p : Prop) (q : Prop) : term1277 p q.
Proof. exact (fun p' : Prop => @lem3934169 p q p'). Qed.
Lemma lem3934171 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) : term1381 A B s t _45772.
Proof. exact (@lem3934170 (@IN A _45772 s) (term1346 A B t _45772)). Qed.
Lemma lem3934172 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) : term1382 A B s t _45772 p'.
Proof. exact (@lem3934171 A B s t _45772 p'). Qed.
Lemma lem3934173 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) : (term1382 A B s t _45772 p') = (term1383 A B s t _45772 p').
Proof. exact (eq_refl (term1382 A B s t _45772 p')). Qed.
Lemma lem3934174 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) : term1383 A B s t _45772 p'.
Proof. exact (EQ_MP (@lem3934173 A B s t _45772 p') (@lem3934172 A B s t _45772 p')). Qed.
Lemma lem3934175 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) (q' : Prop) : term1384 A B s t _45772 p' q'.
Proof. exact (@lem3934174 A B s t _45772 p' q'). Qed.
Lemma lem3934176 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) (q' : Prop) : (term1384 A B s t _45772 p' q') = (term1385 A B s t _45772 p' q').
Proof. exact (eq_refl (term1384 A B s t _45772 p' q')). Qed.
Lemma lem3934177 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_45772 : A) (p' : Prop) (q' : Prop) : term1385 A B s t _45772 p' q'.
Proof. exact (EQ_MP (@lem3934176 A B s t _45772 p' q') (@lem3934175 A B s t _45772 p' q')). Qed.
Lemma lem3934178 {A : Type'} (_45772 : A) (s : A -> Prop) : (@IN A _45772 s) = (@IN A _45772 s).
Proof. exact (eq_refl (@IN A _45772 s)). Qed.
Lemma lem3934179 {A B : Type'} (t : type1413 A B) (_45772 : A) (s : A -> Prop) (q' : Prop) : term1386 A B t _45772 s q'.
Proof. exact (@lem3934177 A B s t _45772 (@IN A _45772 s) q'). Qed.
Lemma lem3934180 {A B : Type'} (t : type1413 A B) (_45772 : A) (s : A -> Prop) (q' : Prop) : term1387 A B t _45772 s q'.
Proof. exact (@lem3934179 A B t _45772 s q' (@lem3934178 A _45772 s)). Qed.
Lemma lem3934181 {A : Type'} (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : @IN A _45772 s.
Proof. exact (h1). Qed.
Lemma lem3934182 {A : Type'} (_45772 : A) (s : A -> Prop) : (@IN A _45772 s) = ((@IN A _45772 s) = True).
Proof. exact (@lem7 (@IN A _45772 s)). Qed.
Lemma lem3934185 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (fun h0 : term549 A x' x s => @lem3934079 A B t n x' x s h1 h0). Qed.
Lemma lem3934186 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (@lem3934185 A B x' x s t n h1). Qed.
Lemma lem3934187 {A B : Type'} (_45772 : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t _45772.
Proof. exact (@lem3934186 A B _45772 x s t n h1). Qed.
Lemma lem3934189 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3934009 A y x s) (@lem3934008 A y x s)). Qed.
Lemma lem3934190 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (@lem3934189 A y x s). Qed.
Lemma lem3934191 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) : (term549 A _45772 x s) = (term556 A x _45772 s).
Proof. exact (@lem3934190 A x _45772 s). Qed.
Lemma lem3934197 {A : Type'} (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : (@IN A _45772 s) = True.
Proof. exact (EQ_MP (@lem3934182 A _45772 s) (@lem3934181 A _45772 s h1)). Qed.
Lemma lem3934198 {A : Type'} (_45772 : A) (x : A) : (term557 A _45772 x) = (term557 A _45772 x).
Proof. exact (eq_refl (term557 A _45772 x)). Qed.
Lemma lem3934199 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : (term556 A x _45772 s) = (term1388 A _45772 x).
Proof. exact (MK_COMB (@lem3934198 A _45772 x) (@lem3934197 A _45772 s h1)). Qed.
Lemma lem3934201 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3934202 {A : Type'} (_45772 : A) (x : A) : (term1388 A _45772 x) = True.
Proof. exact (@lem3934201 (_45772 = x)). Qed.
Lemma lem3934203 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : (term556 A x _45772 s) = True.
Proof. exact (TRANS (@lem3934199 A x _45772 s h1) (@lem3934202 A _45772 x)). Qed.
Lemma lem3934204 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : (term549 A _45772 x s) = True.
Proof. exact (TRANS (@lem3934191 A x _45772 s) (@lem3934203 A x _45772 s h1)). Qed.
Lemma lem3934205 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : True = (term549 A _45772 x s).
Proof. exact (SYM (@lem3934204 A x _45772 s h1)). Qed.
Lemma lem3934206 {A : Type'} (x : A) (_45772 : A) (s : A -> Prop) (h1 : @IN A _45772 s) : term549 A _45772 x s.
Proof. exact (EQ_MP (@lem3934205 A x _45772 s h1) (@lem0)). Qed.
Lemma lem3934207 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (_45772 : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A _45772 s) : (term1346 A B t _45772) = True.
Proof. exact (@lem3934187 A B _45772 x s t n h1 (@lem3934206 A x _45772 s h2)). Qed.
Lemma lem3934208 {A B : Type'} (_45772 : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1389 A B s t _45772.
Proof. exact (fun h0 : @IN A _45772 s => @lem3934207 A B x t n _45772 s h1 h0). Qed.
Lemma lem3934209 {A B : Type'} (t : type1413 A B) (_45772 : A) (s : A -> Prop) : term1390 A B t _45772 s.
Proof. exact (@lem3934180 A B t _45772 s True). Qed.
Lemma lem3934210 {A B : Type'} (_45772 : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1391 A B s t _45772) = (term1392 A _45772 s).
Proof. exact (@lem3934209 A B t _45772 s (@lem3934208 A B _45772 x s t n h1)). Qed.
Lemma lem3934212 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3934213 {A : Type'} (_45772 : A) (s : A -> Prop) : (term1392 A _45772 s) = True.
Proof. exact (@lem3934212 (@IN A _45772 s)). Qed.
Lemma lem3934214 {A B : Type'} (_45772 : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1391 A B s t _45772) = True.
Proof. exact (TRANS (@lem3934210 A B _45772 x s t n h1) (@lem3934213 A _45772 s)). Qed.
Lemma lem3934217 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1393 A B s t) = (term1070 A).
Proof. exact (fun_ext (fun _45772 : A => @lem3934214 A B _45772 x s t n h1)). Qed.
Lemma lem3934218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3934219 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1380 A B s t) = (term1071 A).
Proof. exact (MK_COMB (@lem3934218 A) (@lem3934217 A B x s t n h1)). Qed.
Lemma lem3934221 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3934222 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (@lem3934221 A t). Qed.
Lemma lem3934223 {A : Type'} : (term1071 A) = True.
Proof. exact (@lem3934222 A True). Qed.
Lemma lem3934224 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1380 A B s t) = True.
Proof. exact (TRANS (@lem3934219 A B x s t n h1) (@lem3934223 A)). Qed.
Lemma lem3934225 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1377 A B t s) = True.
Proof. exact (TRANS (@lem3934104 A B s t) (@lem3934224 A B x s t n h1)). Qed.
Lemma lem3934226 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) : (term1358 A B t s) = True.
Proof. exact (TRANS (@lem3934100 A B t s h2) (@lem3934225 A B x s t n h1)). Qed.
Lemma lem3934227 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) : True = (term1358 A B t s).
Proof. exact (SYM (@lem3934226 A B x t n s h1 h2)). Qed.
Lemma lem3934228 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) : term1358 A B t s.
Proof. exact (EQ_MP (@lem3934227 A B x t n s h1 h2) (@lem0)). Qed.
Lemma lem3934229 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) : term1353 A B s t.
Proof. exact (EQ_MP (@lem3934001 A B s t) (@lem3934228 A B x t n s h1 h2)). Qed.
Lemma lem3934230 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1354 A B x s t.
Proof. exact (EQ_MP (@lem3933993 A B t n x s h1 h3) (@lem3934229 A B x t n s h1 h2)). Qed.
Lemma lem3934231 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1394 A B x s t.
Proof. exact (@lem3933896 A B x s t (@lem3934230 A B t n x s h1 h2 h3)). Qed.
Lemma lem3934233 (a : nat) (b : nat) (x : nat) (n : nat) : term8 a b x n.
Proof. exact (@lem3928622 a b x n (@lem3928614 a b x n)). Qed.
Lemma lem3934234 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : term1395 A B x t s n.
Proof. exact (@lem3934233 (term1396 A B t x) (term1397 A B s t) (@CARD A s) n). Qed.
Lemma lem3934235 {A : Type'} (x : A) : term1338 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3934236 {A : Type'} (x : A) : (term1338 A x) = (term1339 A x).
Proof. exact (eq_refl (term1338 A x)). Qed.
Lemma lem3934237 {A : Type'} (x : A) : term1339 A x.
Proof. exact (EQ_MP (@lem3934236 A x) (@lem3934235 A x)). Qed.
Lemma lem3934238 {A : Type'} (x : A) (y : A) : term1340 A x y.
Proof. exact (@lem3934237 A x y). Qed.
Lemma lem3934239 {A : Type'} (y : A) (x : A) : (term1340 A x y) = (term1341 A y x).
Proof. exact (eq_refl (term1340 A x y)). Qed.
Lemma lem3934240 {A : Type'} (y : A) (x : A) : term1341 A y x.
Proof. exact (EQ_MP (@lem3934239 A y x) (@lem3934238 A x y)). Qed.
Lemma lem3934241 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term1342 A y x s.
Proof. exact (@lem3934240 A y x s). Qed.
Lemma lem3934242 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term1342 A y x s) = ((term549 A x y s) = (term556 A y x s)).
Proof. exact (eq_refl (term1342 A y x s)). Qed.
Lemma lem3934244 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term1201 A B s) : term1194 A B s t.
Proof. exact (@lem3933832 A B s h1 t). Qed.
Lemma lem3934245 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1194 A B s t) = (term1185 A B s t).
Proof. exact (eq_refl (term1194 A B s t)). Qed.
Lemma lem3934246 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term1201 A B s) : term1185 A B s t.
Proof. exact (EQ_MP (@lem3934245 A B s t) (@lem3934244 A B t s h1)). Qed.
Lemma lem3934247 {A B : Type'} (t : type1413 A B) (m : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1178 A B s t m.
Proof. exact (@lem3934246 A B t s h1 m). Qed.
Lemma lem3934248 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term1178 A B s t m) = (term1171 A B s t m).
Proof. exact (eq_refl (term1178 A B s t m)). Qed.
Lemma lem3934249 {A B : Type'} (t : type1413 A B) (m : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1171 A B s t m.
Proof. exact (EQ_MP (@lem3934248 A B s t m) (@lem3934247 A B t m s h1)). Qed.
Lemma lem3934250 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1162 A B s t m n.
Proof. exact (@lem3934249 A B t m s h1 n). Qed.
Lemma lem3934251 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1162 A B s t m n) = (term1163 A B s t m n).
Proof. exact (eq_refl (term1162 A B s t m n)). Qed.
Lemma lem3934252 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1163 A B s t m n.
Proof. exact (EQ_MP (@lem3934251 A B s t m n) (@lem3934250 A B t m n s h1)). Qed.
Lemma lem3934253 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1148 A B m s t n) : term1148 A B m s t n.
Proof. exact (h1). Qed.
Lemma lem3934254 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1201 A B s) (h2 : term1148 A B m s t n) : term1115 A B s t m n.
Proof. exact (@lem3934252 A B t m n s h1 (@lem3934253 A B m s t n h2)). Qed.
Lemma lem3934255 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1115 A B s t m n) = ((term1115 A B s t m n) = True).
Proof. exact (@lem7 (term1115 A B s t m n)). Qed.
Lemma lem3934256 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1201 A B s) (h2 : term1148 A B m s t n) : (term1115 A B s t m n) = True.
Proof. exact (EQ_MP (@lem3934255 A B s t m n) (@lem3934254 A B m s t n h1 h2)). Qed.
Lemma lem3934262 {A : Type'} (x : A) (s : A -> Prop) : term1274 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3934266 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1343 A B x s t n x'.
Proof. exact (@lem3933803 A B x s t n h1 x'). Qed.
Lemma lem3934267 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term1343 A B x s t n x') = (term1344 A B x s t x' n).
Proof. exact (eq_refl (term1343 A B x s t n x')). Qed.
Lemma lem3934268 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1344 A B x s t x' n.
Proof. exact (EQ_MP (@lem3934267 A B x s t x' n) (@lem3934266 A B x' x s t n h1)). Qed.
Lemma lem3934269 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term549 A x' x s) : term549 A x' x s.
Proof. exact (h1). Qed.
Lemma lem3934270 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1345 A B t x' n.
Proof. exact (@lem3934268 A B x' x s t n h1 (@lem3934269 A x' x s h2)). Qed.
Lemma lem3934271 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1398 A B t x' n.
Proof. exact (proj2 (@lem3934270 A B t n x' x s h1 h2)). Qed.
Lemma lem3934272 {A B : Type'} (t : type1413 A B) (x' : A) (n : nat) : (term1398 A B t x' n) = ((term1398 A B t x' n) = True).
Proof. exact (@lem7 (term1398 A B t x' n)). Qed.
Lemma lem3934273 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : (term1398 A B t x' n) = True.
Proof. exact (EQ_MP (@lem3934272 A B t x' n) (@lem3934271 A B t n x' x s h1 h2)). Qed.
Lemma lem3934279 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : term1346 A B t x'.
Proof. exact (proj1 (@lem3934270 A B t n x' x s h1 h2)). Qed.
Lemma lem3934280 {A B : Type'} (t : type1413 A B) (x' : A) : (term1346 A B t x') = ((term1346 A B t x') = True).
Proof. exact (@lem7 (term1346 A B t x')). Qed.
Lemma lem3934281 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term549 A x' x s) : (term1346 A B t x') = True.
Proof. exact (EQ_MP (@lem3934280 A B t x') (@lem3934279 A B t n x' x s h1 h2)). Qed.
Lemma lem3934290 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1399 A B x s t x' n.
Proof. exact (fun h0 : term549 A x' x s => @lem3934273 A B t n x' x s h1 h0). Qed.
Lemma lem3934291 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1399 A B x s t x' n.
Proof. exact (@lem3934290 A B x' x s t n h1). Qed.
Lemma lem3934292 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1400 A B s t x n.
Proof. exact (@lem3934291 A B x x s t n h1). Qed.
Lemma lem3934294 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3934242 A y x s) (@lem3934241 A y x s)). Qed.
Lemma lem3934295 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (@lem3934294 A y x s). Qed.
Lemma lem3934296 {A : Type'} (x : A) (s : A -> Prop) : (term1349 A x s) = (term1350 A x s).
Proof. exact (@lem3934295 A x x s). Qed.
Lemma lem3934300 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3934301 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3934300 A x). Qed.
Lemma lem3934302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3934303 {A : Type'} (x : A) : (term1351 A x) = (or True).
Proof. exact (MK_COMB (@lem3934302) (@lem3934301 A x)). Qed.
Lemma lem3934305 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (@IN A x s) = False.
Proof. exact (@lem3934262 A x s (@lem3933846 A x s h1)). Qed.
Lemma lem3934306 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1350 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem3934303 A x) (@lem3934305 A x s h1)). Qed.
Lemma lem3934308 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3934309 : (True \/ False) = True.
Proof. exact (@lem3934308 False). Qed.
Lemma lem3934310 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1350 A x s) = True.
Proof. exact (TRANS (@lem3934306 A x s h1) (@lem3934309)). Qed.
Lemma lem3934311 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : (term1349 A x s) = True.
Proof. exact (TRANS (@lem3934296 A x s) (@lem3934310 A x s h1)). Qed.
Lemma lem3934312 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : True = (term1349 A x s).
Proof. exact (SYM (@lem3934311 A x s h1)). Qed.
Lemma lem3934313 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1266 A x s) : term1349 A x s.
Proof. exact (EQ_MP (@lem3934312 A x s h1) (@lem0)). Qed.
Lemma lem3934314 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1398 A B t x n) = True.
Proof. exact (@lem3934292 A B x s t n h1 (@lem3934313 A x s h2)). Qed.
Lemma lem3934315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3934316 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1266 A x s) : (term1401 A B t x n) = (and True).
Proof. exact (MK_COMB (@lem3934315) (@lem3934314 A B t n x s h1 h2)). Qed.
Lemma lem3934318 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1402 A B s t m n.
Proof. exact (fun h0 : term1148 A B m s t n => @lem3934256 A B m s t n h1 h0). Qed.
Lemma lem3934319 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1402 A B s t m n.
Proof. exact (@lem3934318 A B t m n s h1). Qed.
Lemma lem3934320 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1201 A B s) : term1403 A B t s n.
Proof. exact (@lem3934319 A B t (@CARD A s) n s h1). Qed.
Lemma lem3934324 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3934325 (x : nat) : (x = x) = True.
Proof. exact (@lem3934324 nat x). Qed.
Lemma lem3934326 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem3934325 (@CARD A s)). Qed.
Lemma lem3934327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3934328 {A : Type'} (s : A -> Prop) : (term1404 A s) = (and True).
Proof. exact (MK_COMB (@lem3934327) (@lem3934326 A s)). Qed.
Lemma lem3934336 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1275 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3934337 (p : Prop) (q : Prop) (p' : Prop) : term1276 p q p'.
Proof. exact (fun q' : Prop => @lem3934336 p q p' q'). Qed.
Lemma lem3934338 (p : Prop) (q : Prop) : term1277 p q.
Proof. exact (fun p' : Prop => @lem3934337 p q p'). Qed.
Lemma lem3934339 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) : term1405 A B s t y n.
Proof. exact (@lem3934338 (@IN A y s) (term1345 A B t y n)). Qed.
Lemma lem3934340 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) : term1406 A B s t y n p'.
Proof. exact (@lem3934339 A B s t y n p'). Qed.
Lemma lem3934341 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) : (term1406 A B s t y n p') = (term1407 A B s t y n p').
Proof. exact (eq_refl (term1406 A B s t y n p')). Qed.
Lemma lem3934342 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) : term1407 A B s t y n p'.
Proof. exact (EQ_MP (@lem3934341 A B s t y n p') (@lem3934340 A B s t y n p')). Qed.
Lemma lem3934343 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) (q' : Prop) : term1408 A B s t y n p' q'.
Proof. exact (@lem3934342 A B s t y n p' q'). Qed.
Lemma lem3934344 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) (q' : Prop) : (term1408 A B s t y n p' q') = (term1409 A B s t y n p' q').
Proof. exact (eq_refl (term1408 A B s t y n p' q')). Qed.
Lemma lem3934345 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (y : A) (n : nat) (p' : Prop) (q' : Prop) : term1409 A B s t y n p' q'.
Proof. exact (EQ_MP (@lem3934344 A B s t y n p' q') (@lem3934343 A B s t y n p' q')). Qed.
Lemma lem3934346 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = (@IN A y s).
Proof. exact (eq_refl (@IN A y s)). Qed.
Lemma lem3934347 {A B : Type'} (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (q' : Prop) : term1410 A B t n y s q'.
Proof. exact (@lem3934345 A B s t y n (@IN A y s) q'). Qed.
Lemma lem3934348 {A B : Type'} (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (q' : Prop) : term1411 A B t n y s q'.
Proof. exact (@lem3934347 A B t n y s q' (@lem3934346 A y s)). Qed.
Lemma lem3934349 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : @IN A y s.
Proof. exact (h1). Qed.
Lemma lem3934350 {A : Type'} (y : A) (s : A -> Prop) : (@IN A y s) = ((@IN A y s) = True).
Proof. exact (@lem7 (@IN A y s)). Qed.
Lemma lem3934355 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (fun h0 : term549 A x' x s => @lem3934281 A B t n x' x s h1 h0). Qed.
Lemma lem3934356 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t x'.
Proof. exact (@lem3934355 A B x' x s t n h1). Qed.
Lemma lem3934357 {A B : Type'} (y : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1347 A B x s t y.
Proof. exact (@lem3934356 A B y x s t n h1). Qed.
Lemma lem3934359 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3934242 A y x s) (@lem3934241 A y x s)). Qed.
Lemma lem3934360 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (@lem3934359 A y x s). Qed.
Lemma lem3934361 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term549 A y x s) = (term556 A x y s).
Proof. exact (@lem3934360 A x y s). Qed.
Lemma lem3934367 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : (@IN A y s) = True.
Proof. exact (EQ_MP (@lem3934350 A y s) (@lem3934349 A y s h1)). Qed.
Lemma lem3934368 {A : Type'} (y : A) (x : A) : (term557 A y x) = (term557 A y x).
Proof. exact (eq_refl (term557 A y x)). Qed.
Lemma lem3934369 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term556 A x y s) = (term1388 A y x).
Proof. exact (MK_COMB (@lem3934368 A y x) (@lem3934367 A y s h1)). Qed.
Lemma lem3934371 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3934372 {A : Type'} (y : A) (x : A) : (term1388 A y x) = True.
Proof. exact (@lem3934371 (y = x)). Qed.
Lemma lem3934373 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term556 A x y s) = True.
Proof. exact (TRANS (@lem3934369 A x y s h1) (@lem3934372 A y x)). Qed.
Lemma lem3934374 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term549 A y x s) = True.
Proof. exact (TRANS (@lem3934361 A x y s) (@lem3934373 A x y s h1)). Qed.
Lemma lem3934375 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : True = (term549 A y x s).
Proof. exact (SYM (@lem3934374 A x y s h1)). Qed.
Lemma lem3934376 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : term549 A y x s.
Proof. exact (EQ_MP (@lem3934375 A x y s h1) (@lem0)). Qed.
Lemma lem3934377 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A y s) : (term1346 A B t y) = True.
Proof. exact (@lem3934357 A B y x s t n h1 (@lem3934376 A x y s h2)). Qed.
Lemma lem3934378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3934379 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A y s) : (term1352 A B t y) = (and True).
Proof. exact (MK_COMB (@lem3934378) (@lem3934377 A B x t n y s h1 h2)). Qed.
Lemma lem3934381 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1399 A B x s t x' n.
Proof. exact (fun h0 : term549 A x' x s => @lem3934273 A B t n x' x s h1 h0). Qed.
Lemma lem3934382 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1399 A B x s t x' n.
Proof. exact (@lem3934381 A B x' x s t n h1). Qed.
Lemma lem3934383 {A B : Type'} (y : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1399 A B x s t y n.
Proof. exact (@lem3934382 A B y x s t n h1). Qed.
Lemma lem3934385 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (EQ_MP (@lem3934242 A y x s) (@lem3934241 A y x s)). Qed.
Lemma lem3934386 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term549 A x y s) = (term556 A y x s).
Proof. exact (@lem3934385 A y x s). Qed.
Lemma lem3934387 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term549 A y x s) = (term556 A x y s).
Proof. exact (@lem3934386 A x y s). Qed.
Lemma lem3934393 {A : Type'} (y : A) (s : A -> Prop) (h1 : @IN A y s) : (@IN A y s) = True.
Proof. exact (EQ_MP (@lem3934350 A y s) (@lem3934349 A y s h1)). Qed.
Lemma lem3934394 {A : Type'} (y : A) (x : A) : (term557 A y x) = (term557 A y x).
Proof. exact (eq_refl (term557 A y x)). Qed.
Lemma lem3934395 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term556 A x y s) = (term1388 A y x).
Proof. exact (MK_COMB (@lem3934394 A y x) (@lem3934393 A y s h1)). Qed.
Lemma lem3934397 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3934398 {A : Type'} (y : A) (x : A) : (term1388 A y x) = True.
Proof. exact (@lem3934397 (y = x)). Qed.
Lemma lem3934399 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term556 A x y s) = True.
Proof. exact (TRANS (@lem3934395 A x y s h1) (@lem3934398 A y x)). Qed.
Lemma lem3934400 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : (term549 A y x s) = True.
Proof. exact (TRANS (@lem3934387 A x y s) (@lem3934399 A x y s h1)). Qed.
Lemma lem3934401 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : True = (term549 A y x s).
Proof. exact (SYM (@lem3934400 A x y s h1)). Qed.
Lemma lem3934402 {A : Type'} (x : A) (y : A) (s : A -> Prop) (h1 : @IN A y s) : term549 A y x s.
Proof. exact (EQ_MP (@lem3934401 A x y s h1) (@lem0)). Qed.
Lemma lem3934403 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A y s) : (term1398 A B t y n) = True.
Proof. exact (@lem3934383 A B y x s t n h1 (@lem3934402 A x y s h2)). Qed.
Lemma lem3934404 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A y s) : (term1345 A B t y n) = (True /\ True).
Proof. exact (MK_COMB (@lem3934379 A B x t n y s h1 h2) (@lem3934403 A B x t n y s h1 h2)). Qed.
Lemma lem3934406 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3934407 : (True /\ True) = True.
Proof. exact (@lem3934406 True). Qed.
Lemma lem3934408 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : @IN A y s) : (term1345 A B t y n) = True.
Proof. exact (TRANS (@lem3934404 A B x t n y s h1 h2) (@lem3934407)). Qed.
Lemma lem3934409 {A B : Type'} (y : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1412 A B s t y n.
Proof. exact (fun h0 : @IN A y s => @lem3934408 A B x t n y s h1 h0). Qed.
Lemma lem3934410 {A B : Type'} (t : type1413 A B) (n : nat) (y : A) (s : A -> Prop) : term1413 A B t n y s.
Proof. exact (@lem3934348 A B t n y s True). Qed.
Lemma lem3934411 {A B : Type'} (y : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1414 A B s t y n) = (term1392 A y s).
Proof. exact (@lem3934410 A B t n y s (@lem3934409 A B y x s t n h1)). Qed.
Lemma lem3934413 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3934414 {A : Type'} (y : A) (s : A -> Prop) : (term1392 A y s) = True.
Proof. exact (@lem3934413 (@IN A y s)). Qed.
Lemma lem3934415 {A B : Type'} (y : A) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1414 A B s t y n) = True.
Proof. exact (TRANS (@lem3934411 A B y x s t n h1) (@lem3934414 A y s)). Qed.
Lemma lem3934416 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1415 A B s t n) = (term1070 A).
Proof. exact (fun_ext (fun y : A => @lem3934415 A B y x s t n h1)). Qed.
Lemma lem3934417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3934418 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1110 A B s t n) = (term1071 A).
Proof. exact (MK_COMB (@lem3934417 A) (@lem3934416 A B x s t n h1)). Qed.
Lemma lem3934420 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3934421 {A : Type'} (t : Prop) : (term1072 A t) = t.
Proof. exact (@lem3934420 A t). Qed.
Lemma lem3934422 {A : Type'} : (term1071 A) = True.
Proof. exact (@lem3934421 A True). Qed.
Lemma lem3934423 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1110 A B s t n) = True.
Proof. exact (TRANS (@lem3934418 A B x s t n h1) (@lem3934422 A)). Qed.
Lemma lem3934424 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1416 A B s t n) = (True /\ True).
Proof. exact (MK_COMB (@lem3934328 A s) (@lem3934423 A B x s t n h1)). Qed.
Lemma lem3934426 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3934427 : (True /\ True) = True.
Proof. exact (@lem3934426 True). Qed.
Lemma lem3934428 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : (term1416 A B s t n) = True.
Proof. exact (TRANS (@lem3934424 A B x s t n h1) (@lem3934427)). Qed.
Lemma lem3934429 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : True = (term1416 A B s t n).
Proof. exact (SYM (@lem3934428 A B x s t n h1)). Qed.
Lemma lem3934430 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1310 A B x s t n) : term1416 A B s t n.
Proof. exact (EQ_MP (@lem3934429 A B x s t n h1) (@lem0)). Qed.
Lemma lem3934431 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) : (term1417 A B t s n) = True.
Proof. exact (@lem3934320 A B t n s h2 (@lem3934430 A B x s t n h1)). Qed.
Lemma lem3934432 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : term1266 A x s) : (term1418 A B x t s n) = (True /\ True).
Proof. exact (MK_COMB (@lem3934316 A B t n x s h1 h3) (@lem3934431 A B x t n s h1 h2)). Qed.
Lemma lem3934434 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3934435 : (True /\ True) = True.
Proof. exact (@lem3934434 True). Qed.
Lemma lem3934436 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : term1266 A x s) : (term1418 A B x t s n) = True.
Proof. exact (TRANS (@lem3934432 A B t n x s h1 h2 h3) (@lem3934435)). Qed.
Lemma lem3934437 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : term1266 A x s) : True = (term1418 A B x t s n).
Proof. exact (SYM (@lem3934436 A B t n x s h1 h2 h3)). Qed.
Lemma lem3934438 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : term1266 A x s) : term1418 A B x t s n.
Proof. exact (EQ_MP (@lem3934437 A B t n x s h1 h2 h3) (@lem0)). Qed.
Lemma lem3934439 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : term1266 A x s) : term1419 A B x t s n.
Proof. exact (@lem3934234 A B x t s n (@lem3934438 A B t n x s h1 h2 h3)). Qed.
Lemma lem3934440 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1420 A B x t s n.
Proof. exact (conj (@lem3934231 A B t n x s h1 h3 h4) (@lem3934439 A B t n x s h1 h2 h4)). Qed.
Lemma lem3934441 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1421 A B x t s n.
Proof. exact (ex_intro (term1422 A B x t s n) (term1423 A B x s t) (@lem3934440 A B t n x s h1 h2 h3 h4)). Qed.
Lemma lem3934442 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1331 A B x t s n.
Proof. exact (@lem3933878 A B x t s n (@lem3934441 A B t n x s h1 h2 h3 h4)). Qed.
Lemma lem3934443 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1321 A B x t s n.
Proof. exact (EQ_MP (@lem3933875 A B x t s n) (@lem3934442 A B t n x s h1 h2 h3 h4)). Qed.
Lemma lem3934444 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1311 A B m x s t n) : term1310 A B x s t n.
Proof. exact (proj2 (@lem3933802 A B m x s t n h1)). Qed.
Lemma lem3934445 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1311 A B m x s t n) : (term1291 A s) = m.
Proof. exact (proj1 (@lem3933802 A B m x s t n h1)). Qed.
Lemma lem3934446 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : (term1310 A B x s t n) = (term1321 A B x t s n).
Proof. exact (prop_ext (fun h5 : term1310 A B x s t n => @lem3934443 A B t n x s h1 h2 h3 h4) (fun h5 : term1321 A B x t s n => @lem3933803 A B x s t n h1)). Qed.
Lemma lem3934447 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1321 A B x t s n.
Proof. exact (EQ_MP (@lem3934446 A B t n x s h1 h2 h3 h4) (@lem3933803 A B x s t n h1)). Qed.
Lemma lem3934448 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : (@FINITE A s) = (term1321 A B x t s n).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem3934447 A B t n x s h1 h2 h3 h4) (fun h5 : term1321 A B x t s n => @lem3933860 A s h3)). Qed.
Lemma lem3934449 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1321 A B x t s n.
Proof. exact (EQ_MP (@lem3934448 A B t n x s h1 h2 h3 h4) (@lem3933860 A s h3)). Qed.
Lemma lem3934450 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : (term1266 A x s) = (term1321 A B x t s n).
Proof. exact (prop_ext (fun h5 : term1266 A x s => @lem3934449 A B t n x s h1 h2 h3 h4) (fun h5 : term1321 A B x t s n => @lem3933846 A x s h4)). Qed.
Lemma lem3934451 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1321 A B x t s n.
Proof. exact (EQ_MP (@lem3934450 A B t n x s h1 h2 h3 h4) (@lem3933846 A x s h4)). Qed.
Lemma lem3934452 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : (term1201 A B s) = (term1321 A B x t s n).
Proof. exact (prop_ext (fun h5 : term1201 A B s => @lem3934451 A B t n x s h1 h2 h3 h4) (fun h5 : term1321 A B x t s n => @lem3933832 A B s h2)). Qed.
Lemma lem3934453 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) : term1321 A B x t s n.
Proof. exact (EQ_MP (@lem3934452 A B t n x s h1 h2 h3 h4) (@lem3933832 A B s h2)). Qed.
Lemma lem3934454 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (m : nat) (h1 : term1310 A B x s t n) (h2 : term1201 A B s) (h3 : @FINITE A s) (h4 : term1266 A x s) (h5 : (term1291 A s) = m) : term1280 A B x s t m n.
Proof. exact (EQ_MP (@lem3933818 A B x t n s m h5) (@lem3934453 A B t n x s h1 h2 h3 h4)). Qed.
Lemma lem3934455 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) (h4 : term1311 A B m x s t n) (h5 : (term1291 A s) = m) : (term1310 A B x s t n) = (term1280 A B x s t m n).
Proof. exact (prop_ext (fun h6 : term1310 A B x s t n => @lem3934454 A B t n x s m h6 h1 h2 h3 h5) (fun h6 : term1280 A B x s t m n => @lem3934444 A B m x s t n h4)). Qed.
Lemma lem3934456 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) (h4 : term1311 A B m x s t n) (h5 : (term1291 A s) = m) : term1280 A B x s t m n.
Proof. exact (EQ_MP (@lem3934455 A B x t n s m h1 h2 h3 h4 h5) (@lem3934444 A B m x s t n h4)). Qed.
Lemma lem3934457 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) (h4 : term1311 A B m x s t n) : ((term1291 A s) = m) = (term1280 A B x s t m n).
Proof. exact (prop_ext (fun h5 : (term1291 A s) = m => @lem3934456 A B x t n s m h1 h2 h3 h4 h5) (fun h5 : term1280 A B x s t m n => @lem3934445 A B m x s t n h4)). Qed.
Lemma lem3934458 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) (h4 : term1311 A B m x s t n) : term1280 A B x s t m n.
Proof. exact (EQ_MP (@lem3934457 A B m x s t n h1 h2 h3 h4) (@lem3934445 A B m x s t n h4)). Qed.
Lemma lem3934459 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1317 A B x s t m n.
Proof. exact (fun h0 : term1311 A B m x s t n => @lem3934458 A B m x s t n h1 h2 h3 h0). Qed.
Lemma lem3934460 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1316 A B x s t m n.
Proof. exact (EQ_MP (@lem3933801 A B t m n x s h2 h3) (@lem3934459 A B t m n x s h1 h2 h3)). Qed.
Lemma lem3934465 {A B : Type'} (t : type1413 A B) (m : nat) (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1424 A B x s t m.
Proof. exact (fun n : nat => @lem3934460 A B t m n x s h1 h2 h3). Qed.
Lemma lem3934470 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1425 A B x s t.
Proof. exact (fun m : nat => @lem3934465 A B t m x s h1 h2 h3). Qed.
Lemma lem3934475 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1220 A B x s.
Proof. exact (fun t : type1413 A B => @lem3934470 A B t x s h1 h2 h3). Qed.
Lemma lem3934476 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1216 A B x s) : term1214 A x s.
Proof. exact (proj2 (@lem3933439 A B x s h1)). Qed.
Lemma lem3934477 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1216 A B x s) : term1201 A B s.
Proof. exact (proj1 (@lem3933439 A B x s h1)). Qed.
Lemma lem3934478 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1214 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem3933440 A x s h1)). Qed.
Lemma lem3934479 {A : Type'} (x : A) (s : A -> Prop) (h1 : term1214 A x s) : term1266 A x s.
Proof. exact (proj1 (@lem3933440 A x s h1)). Qed.
Lemma lem3934480 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : (@FINITE A s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3934475 A B x s h1 h2 h3) (fun h4 : term1220 A B x s => @lem3933442 A s h2)). Qed.
Lemma lem3934481 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934480 A B x s h1 h2 h3) (@lem3933442 A s h2)). Qed.
Lemma lem3934482 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : (term1266 A x s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h4 : term1266 A x s => @lem3934481 A B x s h1 h2 h3) (fun h4 : term1220 A B x s => @lem3933443 A x s h3)). Qed.
Lemma lem3934483 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : @FINITE A s) (h3 : term1266 A x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934482 A B x s h1 h2 h3) (@lem3933443 A x s h3)). Qed.
Lemma lem3934484 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1266 A x s) (h3 : term1214 A x s) : (@FINITE A s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3934483 A B x s h1 h4 h2) (fun h4 : term1220 A B x s => @lem3934478 A x s h3)). Qed.
Lemma lem3934485 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1266 A x s) (h3 : term1214 A x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934484 A B x s h1 h2 h3) (@lem3934478 A x s h3)). Qed.
Lemma lem3934486 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1214 A x s) : (term1266 A x s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h3 : term1266 A x s => @lem3934485 A B x s h1 h3 h2) (fun h3 : term1220 A B x s => @lem3934479 A x s h2)). Qed.
Lemma lem3934487 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1214 A x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934486 A B x s h1 h2) (@lem3934479 A x s h2)). Qed.
Lemma lem3934488 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1214 A x s) : (term1201 A B s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h3 : term1201 A B s => @lem3934487 A B x s h1 h2) (fun h3 : term1220 A B x s => @lem3933441 A B s h1)). Qed.
Lemma lem3934489 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1214 A x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934488 A B x s h1 h2) (@lem3933441 A B s h1)). Qed.
Lemma lem3934490 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1216 A B x s) : (term1214 A x s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h3 : term1214 A x s => @lem3934489 A B x s h1 h3) (fun h3 : term1220 A B x s => @lem3934476 A B x s h2)). Qed.
Lemma lem3934491 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1201 A B s) (h2 : term1216 A B x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934490 A B x s h1 h2) (@lem3934476 A B x s h2)). Qed.
Lemma lem3934492 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1216 A B x s) : (term1201 A B s) = (term1220 A B x s).
Proof. exact (prop_ext (fun h2 : term1201 A B s => @lem3934491 A B x s h2 h1) (fun h2 : term1220 A B x s => @lem3934477 A B x s h1)). Qed.
Lemma lem3934493 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term1216 A B x s) : term1220 A B x s.
Proof. exact (EQ_MP (@lem3934492 A B x s h1) (@lem3934477 A B x s h1)). Qed.
Lemma lem3934494 {A B : Type'} (x : A) (s : A -> Prop) : term1222 A B x s.
Proof. exact (fun h0 : term1216 A B x s => @lem3934493 A B x s h0). Qed.
Lemma lem3934499 {A B : Type'} (x : A) : term1226 A B x.
Proof. exact (fun s : A -> Prop => @lem3934494 A B x s). Qed.
Lemma lem3934505 {A B : Type'} : term1230 A B.
Proof. exact (fun x : A => @lem3934499 A B x). Qed.
Lemma lem3934506 {A B : Type'} : term1232 A B.
Proof. exact (conj (@lem3933362 A B) (@lem3934505 A B)). Qed.
Lemma lem3934507 {A B : Type'} : term1204 A B.
Proof. exact (@lem3933272 A B (@lem3934506 A B)). Qed.
Lemma lem3934508 {A B : Type'} : term1156 A B.
Proof. exact (EQ_MP (@lem3933239 A B) (@lem3934507 A B)). Qed.
Lemma lem3934509 {A B : Type'} : term1144 A B.
Proof. exact (EQ_MP (@lem3932927 A B) (@lem3934508 A B)). Qed.
Lemma lem3934510 {A B : Type'} : term1133 A B.
Proof. exact (EQ_MP (@lem3932895 A B) (@lem3934509 A B)). Qed.
Lemma lem3934511 {A B : Type'} : term1132 A B.
Proof. exact (EQ_MP (@lem3932821 A B) (@lem3934510 A B)). Qed.
