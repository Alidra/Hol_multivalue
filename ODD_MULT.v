Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_MULT_term_abbrevs.
Require Import EVEN_MULT_spec.
Require Import NOT_DEF_spec.
Require Import NOT_EVEN_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem127897 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem127898 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem127897 n h1)). Qed.
Lemma lem127899 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem127900 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem127899 n h1)). Qed.
Lemma lem127901 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem127898 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem127900 n h1)). Qed.
Lemma lem127902 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem127901 n)). Qed.
Lemma lem127903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem127904 : term3 = term4.
Proof. exact (MK_COMB (@lem127903) (@lem127902)). Qed.
Lemma lem127905 : term4.
Proof. exact (EQ_MP (@lem127904) (@lem124715)). Qed.
Lemma lem127906 (m : nat) : term5 m.
Proof. exact (@lem126076 m). Qed.
Lemma lem127907 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem127908 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem127907 m) (@lem127906 m)). Qed.
Lemma lem127909 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem127908 m n). Qed.
Lemma lem127910 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = (term9 m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem127912 (n : nat) : term10 n.
Proof. exact (@lem127905 n). Qed.
Lemma lem127913 (n : nat) : (term10 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem127918 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem127913 n) (@lem127912 n)). Qed.
Lemma lem127919 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (@lem127918 (Nat.mul m n)). Qed.
Lemma lem127921 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (EQ_MP (@lem127910 m n) (@lem127909 m n)). Qed.
Lemma lem127924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem127925 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem127924) (@lem127921 m n)). Qed.
Lemma lem127926 (m : nat) (n : nat) : (term11 m n) = (term13 m n).
Proof. exact (TRANS (@lem127919 m n) (@lem127925 m n)). Qed.
Lemma lem127927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem127928 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem127927) (@lem127926 m n)). Qed.
Lemma lem127932 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem127913 n) (@lem127912 n)). Qed.
Lemma lem127933 (m : nat) : (Coq.Arith.PeanoNat.Nat.Odd m) = (term0 m).
Proof. exact (@lem127932 m). Qed.
Lemma lem127934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem127935 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem127934) (@lem127933 m)). Qed.
Lemma lem127937 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem127913 n) (@lem127912 n)). Qed.
Lemma lem127938 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem127935 m) (@lem127937 n)). Qed.
Lemma lem127941 (m : nat) (n : nat) : ((term11 m n) = (term18 m n)) = ((term13 m n) = (term19 m n)).
Proof. exact (MK_COMB (@lem127928 m n) (@lem127938 m n)). Qed.
Lemma lem127944 (m : nat) (n : nat) : ((term13 m n) = (term19 m n)) = ((term11 m n) = (term18 m n)).
Proof. exact (SYM (@lem127941 m n)). Qed.
Lemma lem128010 (m : nat) (n : nat) (h1 : term13 m n) : term13 m n.
Proof. exact (h1). Qed.
Lemma lem128011 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem128012 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem128013 (m : nat) (n : nat) : (term13 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem56) (@lem128012 m n)). Qed.
Lemma lem128014 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem128015 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem128016 (m : nat) (n : nat) : ((term13 m n) = (term20 m n)) = ((term13 m n) = (term21 m n)).
Proof. exact (MK_COMB (@lem128015 m n) (@lem128014 m n)). Qed.
Lemma lem128017 (m : nat) (n : nat) : (term13 m n) = (term21 m n).
Proof. exact (EQ_MP (@lem128016 m n) (@lem128013 m n)). Qed.
Lemma lem128018 (m : nat) (n : nat) (h1 : term13 m n) : term21 m n.
Proof. exact (EQ_MP (@lem128017 m n) (@lem128010 m n h1)). Qed.
Lemma lem128019 (m : nat) (n : nat) (h1 : term9 m n) : term9 m n.
Proof. exact (h1). Qed.
Lemma lem128020 (m : nat) (n : nat) (h1 : term13 m n) (h2 : term9 m n) : False.
Proof. exact (@lem128018 m n h1 (@lem128019 m n h2)). Qed.
Lemma lem128021 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : term9 m n.
Proof. exact (or_intro1 (@lem128011 m h1) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128022 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term13 m n) : (term9 m n) = False.
Proof. exact (prop_ext (fun h3 : term9 m n => @lem128020 m n h2 h3) (fun h3 : False => @lem128021 n m h1)). Qed.
Lemma lem128023 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term13 m n) : False.
Proof. exact (EQ_MP (@lem128022 m n h1 h2) (@lem128021 n m h1)). Qed.
Lemma lem128024 (m : nat) (n : nat) (h1 : term13 m n) : term22 m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem128023 m n h0 h1). Qed.
Lemma lem128025 (m : nat) : (term22 m) = (term0 m).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem128026 (m : nat) (n : nat) (h1 : term13 m n) : term0 m.
Proof. exact (EQ_MP (@lem128025 m) (@lem128024 m n h1)). Qed.
Lemma lem128027 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128028 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem128029 (m : nat) (n : nat) : (term13 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem56) (@lem128028 m n)). Qed.
Lemma lem128030 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem128031 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem128032 (m : nat) (n : nat) : ((term13 m n) = (term20 m n)) = ((term13 m n) = (term21 m n)).
Proof. exact (MK_COMB (@lem128031 m n) (@lem128030 m n)). Qed.
Lemma lem128033 (m : nat) (n : nat) : (term13 m n) = (term21 m n).
Proof. exact (EQ_MP (@lem128032 m n) (@lem128029 m n)). Qed.
Lemma lem128034 (m : nat) (n : nat) (h1 : term13 m n) : term21 m n.
Proof. exact (EQ_MP (@lem128033 m n) (@lem128010 m n h1)). Qed.
Lemma lem128035 (m : nat) (n : nat) (h1 : term9 m n) : term9 m n.
Proof. exact (h1). Qed.
Lemma lem128036 (m : nat) (n : nat) (h1 : term13 m n) (h2 : term9 m n) : False.
Proof. exact (@lem128034 m n h1 (@lem128035 m n h2)). Qed.
Lemma lem128039 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term9 m n.
Proof. exact (or_intro2 (Coq.Arith.PeanoNat.Nat.Even m) (@lem128027 n h1)). Qed.
Lemma lem128040 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term13 m n) : (term9 m n) = False.
Proof. exact (prop_ext (fun h3 : term9 m n => @lem128036 m n h2 h3) (fun h3 : False => @lem128039 m n h1)). Qed.
Lemma lem128041 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term13 m n) : False.
Proof. exact (EQ_MP (@lem128040 m n h1 h2) (@lem128039 m n h1)). Qed.
Lemma lem128042 (m : nat) (n : nat) (h1 : term13 m n) : term22 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem128041 m n h0 h1). Qed.
Lemma lem128043 (n : nat) : (term22 n) = (term0 n).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128044 (m : nat) (n : nat) (h1 : term13 m n) : term0 n.
Proof. exact (EQ_MP (@lem128043 n) (@lem128042 m n h1)). Qed.
Lemma lem128045 (m : nat) (n : nat) (h1 : term13 m n) : term19 m n.
Proof. exact (conj (@lem128026 m n h1) (@lem128044 m n h1)). Qed.
Lemma lem128046 (m : nat) (n : nat) : term23 m n.
Proof. exact (fun h0 : term13 m n => @lem128045 m n h0). Qed.
Lemma lem128047 (m : nat) (n : nat) (h1 : term19 m n) : term19 m n.
Proof. exact (h1). Qed.
Lemma lem128048 (m : nat) (n : nat) (h1 : term9 m n) : term9 m n.
Proof. exact (h1). Qed.
Lemma lem128049 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem128050 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128052 (m : nat) (n : nat) (h1 : term19 m n) : term0 m.
Proof. exact (proj1 (@lem128047 m n h1)). Qed.
Lemma lem128060 (m : nat) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem128061 (m : nat) : (term0 m) = (term24 m).
Proof. exact (MK_COMB (@lem56) (@lem128060 m)). Qed.
Lemma lem128062 (m : nat) : (term24 m) = (term22 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem128063 (m : nat) : (term25 m) = (term25 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem128064 (m : nat) : ((term0 m) = (term24 m)) = ((term0 m) = (term22 m)).
Proof. exact (MK_COMB (@lem128063 m) (@lem128062 m)). Qed.
Lemma lem128065 (m : nat) : (term0 m) = (term22 m).
Proof. exact (EQ_MP (@lem128064 m) (@lem128061 m)). Qed.
Lemma lem128066 (m : nat) (n : nat) (h1 : term19 m n) : term22 m.
Proof. exact (EQ_MP (@lem128065 m) (@lem128052 m n h1)). Qed.
Lemma lem128067 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem128068 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term19 m n) : False.
Proof. exact (@lem128066 m n h2 (@lem128067 m h1)). Qed.
Lemma lem128069 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term19 m n) : (Coq.Arith.PeanoNat.Nat.Even m) = False.
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Even m => @lem128068 m n h1 h2) (fun h3 : False => @lem128049 m h1)). Qed.
Lemma lem128070 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term19 m n) : False.
Proof. exact (EQ_MP (@lem128069 m n h1 h2) (@lem128049 m h1)). Qed.
Lemma lem128071 (m : nat) (n : nat) (h1 : term19 m n) : term0 n.
Proof. exact (proj2 (@lem128047 m n h1)). Qed.
Lemma lem128073 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128074 (n : nat) : (term0 n) = (term24 n).
Proof. exact (MK_COMB (@lem56) (@lem128073 n)). Qed.
Lemma lem128075 (n : nat) : (term24 n) = (term22 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem128076 (n : nat) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem128077 (n : nat) : ((term0 n) = (term24 n)) = ((term0 n) = (term22 n)).
Proof. exact (MK_COMB (@lem128076 n) (@lem128075 n)). Qed.
Lemma lem128078 (n : nat) : (term0 n) = (term22 n).
Proof. exact (EQ_MP (@lem128077 n) (@lem128074 n)). Qed.
Lemma lem128079 (m : nat) (n : nat) (h1 : term19 m n) : term22 n.
Proof. exact (EQ_MP (@lem128078 n) (@lem128071 m n h1)). Qed.
Lemma lem128093 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128094 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term19 m n) : False.
Proof. exact (@lem128079 m n h2 (@lem128093 n h1)). Qed.
Lemma lem128095 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term19 m n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Even n => @lem128094 m n h1 h2) (fun h3 : False => @lem128050 n h1)). Qed.
Lemma lem128096 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term19 m n) : False.
Proof. exact (EQ_MP (@lem128095 m n h1 h2) (@lem128050 n h1)). Qed.
Lemma lem128097 (m : nat) (n : nat) (h1 : term19 m n) (h2 : term9 m n) : False.
Proof. exact (or_elim (@lem128048 m n h2) (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem128070 m n h0 h1) (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem128096 m n h0 h1)). Qed.
Lemma lem128098 (m : nat) (n : nat) (h1 : term19 m n) : term21 m n.
Proof. exact (fun h0 : term9 m n => @lem128097 m n h1 h0). Qed.
Lemma lem128099 (m : nat) (n : nat) : (term21 m n) = (term13 m n).
Proof. exact (@lem69 (term9 m n)). Qed.
Lemma lem128100 (m : nat) (n : nat) (h1 : term19 m n) : term13 m n.
Proof. exact (EQ_MP (@lem128099 m n) (@lem128098 m n h1)). Qed.
Lemma lem128101 (m : nat) (n : nat) : term26 m n.
Proof. exact (fun h0 : term19 m n => @lem128100 m n h0). Qed.
Lemma lem128102 (m : nat) (n : nat) : term27 m n.
Proof. exact (conj (@lem128046 m n) (@lem128101 m n)). Qed.
Lemma lem128103 (m : nat) (n : nat) : (term27 m n) = ((term13 m n) = (term19 m n)).
Proof. exact (@lem32 (term13 m n) (term19 m n)). Qed.
Lemma lem128104 (m : nat) (n : nat) : (term13 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem128103 m n) (@lem128102 m n)). Qed.
Lemma lem128105 (m : nat) (n : nat) : (term11 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem127944 m n) (@lem128104 m n)). Qed.
Lemma lem128110 (m : nat) : term28 m.
Proof. exact (fun n : nat => @lem128105 m n). Qed.
Lemma lem128115 : term29.
Proof. exact (fun m : nat => @lem128110 m). Qed.
