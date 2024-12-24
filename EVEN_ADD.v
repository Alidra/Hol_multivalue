Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import EVEN_OR_ODD_spec.
Require Import NOT_EVEN_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm124233_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem124984 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem124985 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem124984 n h1)). Qed.
Lemma lem124986 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem124987 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem124986 n h1)). Qed.
Lemma lem124988 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem124985 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem124987 n h1)). Qed.
Lemma lem124989 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem124988 n)). Qed.
Lemma lem124990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124991 : term3 = term4.
Proof. exact (MK_COMB (@lem124990) (@lem124989)). Qed.
Lemma lem124992 : term4.
Proof. exact (EQ_MP (@lem124991) (@lem124715)). Qed.
Lemma lem124993 (n : nat) : term5 n.
Proof. exact (@lem124992 n). Qed.
Lemma lem124994 (n : nat) : (term5 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem124996 (p : nat) : term6 p.
Proof. exact (@lem124909 p). Qed.
Lemma lem124997 (p : nat) : (term6 p) = (term7 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem124998 (p : nat) : term7 p.
Proof. exact (EQ_MP (@lem124997 p) (@lem124996 p)). Qed.
Lemma lem124999 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125000 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : Coq.Arith.PeanoNat.Nat.Odd p.
Proof. exact (h1). Qed.
Lemma lem125001 (n : nat) : term6 n.
Proof. exact (@lem124909 n). Qed.
Lemma lem125002 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem125003 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem125002 n) (@lem125001 n)). Qed.
Lemma lem125004 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem125005 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem125007 (P : nat -> Prop) : term8 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem125008 : term9.
Proof. exact (@lem125007 term10). Qed.
Lemma lem125009 : term11 = term12.
Proof. exact (eq_refl term11). Qed.
Lemma lem125010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem125011 : term13 = term14.
Proof. exact (MK_COMB (@lem125010) (@lem125009)). Qed.
Lemma lem125012 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem125013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125014 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem125013) (@lem125012 m)). Qed.
Lemma lem125015 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem125016 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem125014 m) (@lem125015 m)). Qed.
Lemma lem125017 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem125016 m)). Qed.
Lemma lem125018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125019 : term25 = term26.
Proof. exact (MK_COMB (@lem125018) (@lem125017)). Qed.
Lemma lem125020 : term27 = term28.
Proof. exact (MK_COMB (@lem125011) (@lem125019)). Qed.
Lemma lem125021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125022 : term29 = term30.
Proof. exact (MK_COMB (@lem125021) (@lem125020)). Qed.
Lemma lem125023 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem125024 : term31 = term10.
Proof. exact (fun_ext (fun m : nat => @lem125023 m)). Qed.
Lemma lem125025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125026 : term32 = term33.
Proof. exact (MK_COMB (@lem125025) (@lem125024)). Qed.
Lemma lem125027 : term9 = term34.
Proof. exact (MK_COMB (@lem125022) (@lem125026)). Qed.
Lemma lem125028 : term34.
Proof. exact (EQ_MP (@lem125027) (@lem125008)). Qed.
Lemma lem125029 (m : nat) (h1 : term16 m) : term16 m.
Proof. exact (h1). Qed.
Lemma lem125050 : term35.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem125051 (n : nat) : term36 n.
Proof. exact (@lem125050 n). Qed.
Lemma lem125052 (n : nat) : (term36 n) = ((term37 n) = n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem125066 (n : nat) : (term37 n) = n.
Proof. exact (EQ_MP (@lem125052 n) (@lem125051 n)). Qed.
Lemma lem125067 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem125068 (n : nat) : (term38 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (MK_COMB (@lem125067) (@lem125066 n)). Qed.
Lemma lem125069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125070 (n : nat) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem125069) (@lem125068 n)). Qed.
Lemma lem125074 : term41 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem125075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125076 : term42 = (@eq Prop True).
Proof. exact (MK_COMB (@lem125075) (@lem125074)). Qed.
Lemma lem125077 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125078 (n : nat) : (term41 = (Coq.Arith.PeanoNat.Nat.Even n)) = (True = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem125076) (@lem125077 n)). Qed.
Lemma lem125080 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125081 (n : nat) : (True = (Coq.Arith.PeanoNat.Nat.Even n)) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem125080 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125082 (n : nat) : (term41 = (Coq.Arith.PeanoNat.Nat.Even n)) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem125078 n) (@lem125081 n)). Qed.
Lemma lem125083 (n : nat) : ((term38 n) = (term41 = (Coq.Arith.PeanoNat.Nat.Even n))) = ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem125070 n) (@lem125082 n)). Qed.
Lemma lem125085 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125086 (x : Prop) : (x = x) = True.
Proof. exact (@lem125085 Prop x). Qed.
Lemma lem125087 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (@lem125086 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125088 (n : nat) : ((term38 n) = (term41 = (Coq.Arith.PeanoNat.Nat.Even n))) = True.
Proof. exact (TRANS (@lem125083 n) (@lem125087 n)). Qed.
Lemma lem125089 : term43 = term44.
Proof. exact (fun_ext (fun n : nat => @lem125088 n)). Qed.
Lemma lem125090 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125091 : term12 = term45.
Proof. exact (MK_COMB (@lem125090) (@lem125089)). Qed.
Lemma lem125093 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem125094 (t : Prop) : (term47 t) = t.
Proof. exact (@lem125093 nat t). Qed.
Lemma lem125095 : term45 = True.
Proof. exact (@lem125094 True). Qed.
Lemma lem125096 : term12 = True.
Proof. exact (TRANS (@lem125091) (@lem125095)). Qed.
Lemma lem125097 : True = term12.
Proof. exact (SYM (@lem125096)). Qed.
Lemma lem125098 : term12.
Proof. exact (EQ_MP (@lem125097) (@lem0)). Qed.
Lemma lem125099 : term48.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem125100 : term49.
Proof. exact (proj2 (@lem125099)). Qed.
Lemma lem125108 : term50.
Proof. exact (proj1 (@lem125100)). Qed.
Lemma lem125109 (m : nat) : term51 m.
Proof. exact (@lem125108 m). Qed.
Lemma lem125110 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem125111 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem125110 m) (@lem125109 m)). Qed.
Lemma lem125112 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem125111 m n). Qed.
Lemma lem125113 (m : nat) (n : nat) : (term53 m n) = ((term54 m n) = (term55 m n)).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem125123 : term56.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem125124 (n : nat) : term57 n.
Proof. exact (@lem125123 n). Qed.
Lemma lem125125 (n : nat) : (term57 n) = ((term58 n) = (term0 n)).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem125128 (n : nat) (m : nat) (h1 : term16 m) : term59 m n.
Proof. exact (@lem125029 m h1 n). Qed.
Lemma lem125129 (m : nat) (n : nat) : (term59 m n) = ((term60 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem125138 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (EQ_MP (@lem125113 m n) (@lem125112 m n)). Qed.
Lemma lem125139 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem125140 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem125139) (@lem125138 m n)). Qed.
Lemma lem125142 (n : nat) : (term58 n) = (term0 n).
Proof. exact (EQ_MP (@lem125125 n) (@lem125124 n)). Qed.
Lemma lem125143 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (@lem125142 (Nat.add m n)). Qed.
Lemma lem125145 (n : nat) (m : nat) (h1 : term16 m) : (term60 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem125129 m n) (@lem125128 n m h1)). Qed.
Lemma lem125148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem125149 (n : nat) (m : nat) (h1 : term16 m) : (term63 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem125148) (@lem125145 n m h1)). Qed.
Lemma lem125150 (n : nat) (m : nat) (h1 : term16 m) : (term62 m n) = (term64 m n).
Proof. exact (TRANS (@lem125143 m n) (@lem125149 n m h1)). Qed.
Lemma lem125151 (n : nat) (m : nat) (h1 : term16 m) : (term61 m n) = (term64 m n).
Proof. exact (TRANS (@lem125140 m n) (@lem125150 n m h1)). Qed.
Lemma lem125152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125153 (n : nat) (m : nat) (h1 : term16 m) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem125152) (@lem125151 n m h1)). Qed.
Lemma lem125157 (n : nat) : (term58 n) = (term0 n).
Proof. exact (EQ_MP (@lem125125 n) (@lem125124 n)). Qed.
Lemma lem125158 (m : nat) : (term58 m) = (term0 m).
Proof. exact (@lem125157 m). Qed.
Lemma lem125159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125160 (m : nat) : (term67 m) = (term68 m).
Proof. exact (MK_COMB (@lem125159) (@lem125158 m)). Qed.
Lemma lem125161 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125162 (m : nat) (n : nat) : ((term58 m) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem125160 m) (@lem125161 n)). Qed.
Lemma lem125165 (n : nat) (m : nat) (h1 : term16 m) : ((term61 m n) = ((term58 m) = (Coq.Arith.PeanoNat.Nat.Even n))) = ((term64 m n) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (MK_COMB (@lem125153 n m h1) (@lem125162 m n)). Qed.
Lemma lem125168 (m : nat) (h1 : term16 m) : (term69 m) = (term70 m).
Proof. exact (fun_ext (fun n : nat => @lem125165 n m h1)). Qed.
Lemma lem125169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125170 (m : nat) (h1 : term16 m) : (term20 m) = (term71 m).
Proof. exact (MK_COMB (@lem125169) (@lem125168 m h1)). Qed.
Lemma lem125175 (m : nat) (h1 : term16 m) : (term71 m) = (term20 m).
Proof. exact (SYM (@lem125170 m h1)). Qed.
Lemma lem125191 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem124994 n) (@lem124993 n)). Qed.
Lemma lem125192 (p : nat) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term0 p).
Proof. exact (@lem125191 p). Qed.
Lemma lem125193 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125194 (p : nat) : (term72 p) = (term73 p).
Proof. exact (MK_COMB (@lem125193) (@lem125192 p)). Qed.
Lemma lem125203 (n : nat) (m : nat) (p : nat) : (term74 n m p) = (term74 n m p).
Proof. exact (eq_refl (term74 n m p)). Qed.
Lemma lem125204 (n : nat) (m : nat) (p : nat) : (term75 n m p) = (term76 n m p).
Proof. exact (MK_COMB (@lem125194 p) (@lem125203 n m p)). Qed.
Lemma lem125207 (n : nat) (m : nat) (p : nat) : (term76 n m p) = (term75 n m p).
Proof. exact (SYM (@lem125204 n m p)). Qed.
Lemma lem125213 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem124994 n) (@lem124993 n)). Qed.
Lemma lem125214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125215 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem125214) (@lem125213 n)). Qed.
Lemma lem125222 (m : nat) (p : nat) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))).
Proof. exact (eq_refl ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)))). Qed.
Lemma lem125223 (n : nat) (m : nat) (p : nat) : (term77 n m p) = (term78 n m p).
Proof. exact (MK_COMB (@lem125215 n) (@lem125222 m p)). Qed.
Lemma lem125226 (p : nat) : (term79 p) = (term79 p).
Proof. exact (eq_refl (term79 p)). Qed.
Lemma lem125227 (n : nat) (m : nat) (p : nat) : (term80 n m p) = (term81 n m p).
Proof. exact (MK_COMB (@lem125226 p) (@lem125223 n m p)). Qed.
Lemma lem125230 (n : nat) (m : nat) (p : nat) : (term81 n m p) = (term80 n m p).
Proof. exact (SYM (@lem125227 n m p)). Qed.
Lemma lem125234 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem124994 n) (@lem124993 n)). Qed.
Lemma lem125235 (p : nat) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term0 p).
Proof. exact (@lem125234 p). Qed.
Lemma lem125236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125237 (p : nat) : (term72 p) = (term73 p).
Proof. exact (MK_COMB (@lem125236) (@lem125235 p)). Qed.
Lemma lem125241 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem124994 n) (@lem124993 n)). Qed.
Lemma lem125242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125243 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem125242) (@lem125241 n)). Qed.
Lemma lem125250 (m : nat) (p : nat) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))).
Proof. exact (eq_refl ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)))). Qed.
Lemma lem125251 (n : nat) (m : nat) (p : nat) : (term77 n m p) = (term78 n m p).
Proof. exact (MK_COMB (@lem125243 n) (@lem125250 m p)). Qed.
Lemma lem125254 (n : nat) (m : nat) (p : nat) : (term82 n m p) = (term83 n m p).
Proof. exact (MK_COMB (@lem125237 p) (@lem125251 n m p)). Qed.
Lemma lem125257 (n : nat) (m : nat) (p : nat) : (term83 n m p) = (term82 n m p).
Proof. exact (SYM (@lem125254 n m p)). Qed.
Lemma lem125258 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125259 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem125260 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125261 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem125265 (p : nat) : (Coq.Arith.PeanoNat.Nat.Even p) = ((Coq.Arith.PeanoNat.Nat.Even p) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125274 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125265 p) (@lem125258 p h1)). Qed.
Lemma lem125275 (m : nat) : (term40 m) = (term40 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem125276 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = True).
Proof. exact (MK_COMB (@lem125275 m) (@lem125274 p h1)). Qed.
Lemma lem125278 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem125279 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = True) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125278 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125280 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125276 m p h1) (@lem125279 m)). Qed.
Lemma lem125281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem125282 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term64 m p) = (term0 m).
Proof. exact (MK_COMB (@lem125281) (@lem125280 m p h1)). Qed.
Lemma lem125283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125284 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term66 m p) = (term68 m).
Proof. exact (MK_COMB (@lem125283) (@lem125282 m p h1)). Qed.
Lemma lem125288 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125265 p) (@lem125258 p h1)). Qed.
Lemma lem125289 (m : nat) : (term68 m) = (term68 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem125290 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((term0 m) = True).
Proof. exact (MK_COMB (@lem125289 m) (@lem125288 p h1)). Qed.
Lemma lem125292 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem125293 (m : nat) : ((term0 m) = True) = (term0 m).
Proof. exact (@lem125292 (term0 m)). Qed.
Lemma lem125294 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem125290 m p h1) (@lem125293 m)). Qed.
Lemma lem125295 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((term0 m) = (term0 m)).
Proof. exact (MK_COMB (@lem125284 m p h1) (@lem125294 m p h1)). Qed.
Lemma lem125297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125298 (x : Prop) : (x = x) = True.
Proof. exact (@lem125297 Prop x). Qed.
Lemma lem125299 (m : nat) : ((term0 m) = (term0 m)) = True.
Proof. exact (@lem125298 (term0 m)). Qed.
Lemma lem125300 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = True.
Proof. exact (TRANS (@lem125295 m p h1) (@lem125299 m)). Qed.
Lemma lem125301 (n : nat) : (term79 n) = (term79 n).
Proof. exact (eq_refl (term79 n)). Qed.
Lemma lem125302 (m : nat) (n : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term74 n m p) = (term84 n).
Proof. exact (MK_COMB (@lem125301 n) (@lem125300 m p h1)). Qed.
Lemma lem125304 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125305 (n : nat) : (term84 n) = True.
Proof. exact (@lem125304 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125306 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term74 n m p) = True.
Proof. exact (TRANS (@lem125302 m n p h1) (@lem125305 n)). Qed.
Lemma lem125307 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : True = (term74 n m p).
Proof. exact (SYM (@lem125306 n m p h1)). Qed.
Lemma lem125308 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term74 n m p.
Proof. exact (EQ_MP (@lem125307 n m p h1) (@lem0)). Qed.
Lemma lem125312 (p : nat) : term85 p.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125321 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125312 p (@lem125259 p h1)). Qed.
Lemma lem125322 (m : nat) : (term40 m) = (term40 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem125323 (m : nat) (p : nat) (h1 : term0 p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = False).
Proof. exact (MK_COMB (@lem125322 m) (@lem125321 p h1)). Qed.
Lemma lem125325 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem125326 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = False) = (term0 m).
Proof. exact (@lem125325 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125327 (m : nat) (p : nat) (h1 : term0 p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem125323 m p h1) (@lem125326 m)). Qed.
Lemma lem125328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem125329 (m : nat) (p : nat) (h1 : term0 p) : (term64 m p) = (term86 m).
Proof. exact (MK_COMB (@lem125328) (@lem125327 m p h1)). Qed.
Lemma lem125331 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem125332 (m : nat) : (term86 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125331 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125333 (m : nat) (p : nat) (h1 : term0 p) : (term64 m p) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125329 m p h1) (@lem125332 m)). Qed.
Lemma lem125334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125335 (m : nat) (p : nat) (h1 : term0 p) : (term66 m p) = (term40 m).
Proof. exact (MK_COMB (@lem125334) (@lem125333 m p h1)). Qed.
Lemma lem125339 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125312 p (@lem125259 p h1)). Qed.
Lemma lem125340 (m : nat) : (term68 m) = (term68 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem125341 (m : nat) (p : nat) (h1 : term0 p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((term0 m) = False).
Proof. exact (MK_COMB (@lem125340 m) (@lem125339 p h1)). Qed.
Lemma lem125343 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem125344 (m : nat) : ((term0 m) = False) = (term86 m).
Proof. exact (@lem125343 (term0 m)). Qed.
Lemma lem125346 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem125347 (m : nat) : (term86 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125346 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125348 (m : nat) : ((term0 m) = False) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125344 m) (@lem125347 m)). Qed.
Lemma lem125349 (m : nat) (p : nat) (h1 : term0 p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125341 m p h1) (@lem125348 m)). Qed.
Lemma lem125350 (m : nat) (p : nat) (h1 : term0 p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (MK_COMB (@lem125335 m p h1) (@lem125349 m p h1)). Qed.
Lemma lem125352 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125353 (x : Prop) : (x = x) = True.
Proof. exact (@lem125352 Prop x). Qed.
Lemma lem125354 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m)) = True.
Proof. exact (@lem125353 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125355 (m : nat) (p : nat) (h1 : term0 p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = True.
Proof. exact (TRANS (@lem125350 m p h1) (@lem125354 m)). Qed.
Lemma lem125356 (n : nat) : (term79 n) = (term79 n).
Proof. exact (eq_refl (term79 n)). Qed.
Lemma lem125357 (m : nat) (n : nat) (p : nat) (h1 : term0 p) : (term74 n m p) = (term84 n).
Proof. exact (MK_COMB (@lem125356 n) (@lem125355 m p h1)). Qed.
Lemma lem125359 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125360 (n : nat) : (term84 n) = True.
Proof. exact (@lem125359 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125361 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : (term74 n m p) = True.
Proof. exact (TRANS (@lem125357 m n p h1) (@lem125360 n)). Qed.
Lemma lem125362 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : True = (term74 n m p).
Proof. exact (SYM (@lem125361 n m p h1)). Qed.
Lemma lem125363 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : term74 n m p.
Proof. exact (EQ_MP (@lem125362 n m p h1) (@lem0)). Qed.
Lemma lem125367 (p : nat) : (Coq.Arith.PeanoNat.Nat.Even p) = ((Coq.Arith.PeanoNat.Nat.Even p) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125376 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125367 p) (@lem125260 p h1)). Qed.
Lemma lem125377 (m : nat) : (term40 m) = (term40 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem125378 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = True).
Proof. exact (MK_COMB (@lem125377 m) (@lem125376 p h1)). Qed.
Lemma lem125380 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem125381 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = True) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125380 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125382 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125378 m p h1) (@lem125381 m)). Qed.
Lemma lem125383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem125384 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term64 m p) = (term0 m).
Proof. exact (MK_COMB (@lem125383) (@lem125382 m p h1)). Qed.
Lemma lem125385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125386 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term66 m p) = (term68 m).
Proof. exact (MK_COMB (@lem125385) (@lem125384 m p h1)). Qed.
Lemma lem125390 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125367 p) (@lem125260 p h1)). Qed.
Lemma lem125391 (m : nat) : (term68 m) = (term68 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem125392 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((term0 m) = True).
Proof. exact (MK_COMB (@lem125391 m) (@lem125390 p h1)). Qed.
Lemma lem125394 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem125395 (m : nat) : ((term0 m) = True) = (term0 m).
Proof. exact (@lem125394 (term0 m)). Qed.
Lemma lem125396 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem125392 m p h1) (@lem125395 m)). Qed.
Lemma lem125397 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((term0 m) = (term0 m)).
Proof. exact (MK_COMB (@lem125386 m p h1) (@lem125396 m p h1)). Qed.
Lemma lem125399 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125400 (x : Prop) : (x = x) = True.
Proof. exact (@lem125399 Prop x). Qed.
Lemma lem125401 (m : nat) : ((term0 m) = (term0 m)) = True.
Proof. exact (@lem125400 (term0 m)). Qed.
Lemma lem125402 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = True.
Proof. exact (TRANS (@lem125397 m p h1) (@lem125401 m)). Qed.
Lemma lem125403 (n : nat) : (term73 n) = (term73 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem125404 (m : nat) (n : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 n m p) = (term88 n).
Proof. exact (MK_COMB (@lem125403 n) (@lem125402 m p h1)). Qed.
Lemma lem125406 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125407 (n : nat) : (term88 n) = True.
Proof. exact (@lem125406 (term0 n)). Qed.
Lemma lem125408 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 n m p) = True.
Proof. exact (TRANS (@lem125404 m n p h1) (@lem125407 n)). Qed.
Lemma lem125409 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : True = (term78 n m p).
Proof. exact (SYM (@lem125408 n m p h1)). Qed.
Lemma lem125410 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term78 n m p.
Proof. exact (EQ_MP (@lem125409 n m p h1) (@lem0)). Qed.
Lemma lem125414 (p : nat) : term85 p.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125423 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125414 p (@lem125261 p h1)). Qed.
Lemma lem125424 (m : nat) : (term40 m) = (term40 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem125425 (m : nat) (p : nat) (h1 : term0 p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = False).
Proof. exact (MK_COMB (@lem125424 m) (@lem125423 p h1)). Qed.
Lemma lem125427 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem125428 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = False) = (term0 m).
Proof. exact (@lem125427 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125429 (m : nat) (p : nat) (h1 : term0 p) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem125425 m p h1) (@lem125428 m)). Qed.
Lemma lem125430 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem125431 (m : nat) (p : nat) (h1 : term0 p) : (term64 m p) = (term86 m).
Proof. exact (MK_COMB (@lem125430) (@lem125429 m p h1)). Qed.
Lemma lem125433 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem125434 (m : nat) : (term86 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125433 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125435 (m : nat) (p : nat) (h1 : term0 p) : (term64 m p) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125431 m p h1) (@lem125434 m)). Qed.
Lemma lem125436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125437 (m : nat) (p : nat) (h1 : term0 p) : (term66 m p) = (term40 m).
Proof. exact (MK_COMB (@lem125436) (@lem125435 m p h1)). Qed.
Lemma lem125441 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125414 p (@lem125261 p h1)). Qed.
Lemma lem125442 (m : nat) : (term68 m) = (term68 m).
Proof. exact (eq_refl (term68 m)). Qed.
Lemma lem125443 (m : nat) (p : nat) (h1 : term0 p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((term0 m) = False).
Proof. exact (MK_COMB (@lem125442 m) (@lem125441 p h1)). Qed.
Lemma lem125445 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem125446 (m : nat) : ((term0 m) = False) = (term86 m).
Proof. exact (@lem125445 (term0 m)). Qed.
Lemma lem125448 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem125449 (m : nat) : (term86 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125448 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125450 (m : nat) : ((term0 m) = False) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125446 m) (@lem125449 m)). Qed.
Lemma lem125451 (m : nat) (p : nat) (h1 : term0 p) : ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125443 m p h1) (@lem125450 m)). Qed.
Lemma lem125452 (m : nat) (p : nat) (h1 : term0 p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m)).
Proof. exact (MK_COMB (@lem125437 m p h1) (@lem125451 m p h1)). Qed.
Lemma lem125454 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125455 (x : Prop) : (x = x) = True.
Proof. exact (@lem125454 Prop x). Qed.
Lemma lem125456 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m)) = True.
Proof. exact (@lem125455 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125457 (m : nat) (p : nat) (h1 : term0 p) : ((term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p))) = True.
Proof. exact (TRANS (@lem125452 m p h1) (@lem125456 m)). Qed.
Lemma lem125458 (n : nat) : (term73 n) = (term73 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem125459 (m : nat) (n : nat) (p : nat) (h1 : term0 p) : (term78 n m p) = (term88 n).
Proof. exact (MK_COMB (@lem125458 n) (@lem125457 m p h1)). Qed.
Lemma lem125461 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125462 (n : nat) : (term88 n) = True.
Proof. exact (@lem125461 (term0 n)). Qed.
Lemma lem125463 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : (term78 n m p) = True.
Proof. exact (TRANS (@lem125459 m n p h1) (@lem125462 n)). Qed.
Lemma lem125464 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : True = (term78 n m p).
Proof. exact (SYM (@lem125463 n m p h1)). Qed.
Lemma lem125465 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : term78 n m p.
Proof. exact (EQ_MP (@lem125464 n m p h1) (@lem0)). Qed.
Lemma lem125466 (n : nat) (m : nat) (p : nat) : term83 n m p.
Proof. exact (fun h0 : term0 p => @lem125465 n m p h0). Qed.
Lemma lem125467 (n : nat) (m : nat) (p : nat) : term81 n m p.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125410 n m p h0). Qed.
Lemma lem125468 (n : nat) (m : nat) (p : nat) : term76 n m p.
Proof. exact (fun h0 : term0 p => @lem125363 n m p h0). Qed.
Lemma lem125470 (n : nat) (m : nat) (p : nat) : term82 n m p.
Proof. exact (EQ_MP (@lem125257 n m p) (@lem125466 n m p)). Qed.
Lemma lem125471 (n : nat) (m : nat) (p : nat) : term80 n m p.
Proof. exact (EQ_MP (@lem125230 n m p) (@lem125467 n m p)). Qed.
Lemma lem125472 (n : nat) (m : nat) (p : nat) : term75 n m p.
Proof. exact (EQ_MP (@lem125207 n m p) (@lem125468 n m p)). Qed.
Lemma lem125473 (n : nat) (m : nat) (p : nat) : term89 n m p.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125308 n m p h0). Qed.
Lemma lem125474 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : term77 n m p.
Proof. exact (@lem125470 n m p (@lem125000 p h1)). Qed.
Lemma lem125475 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term77 n m p.
Proof. exact (@lem125471 n m p (@lem124999 p h1)). Qed.
Lemma lem125476 (n : nat) (m : nat) (p : nat) : term77 n m p.
Proof. exact (or_elim (@lem124998 p) (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125475 n m p h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd p => @lem125474 n m p h0)). Qed.
Lemma lem125477 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : term74 n m p.
Proof. exact (@lem125472 n m p (@lem125000 p h1)). Qed.
Lemma lem125478 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term74 n m p.
Proof. exact (@lem125473 n m p (@lem124999 p h1)). Qed.
Lemma lem125479 (n : nat) (m : nat) (p : nat) : term74 n m p.
Proof. exact (or_elim (@lem124998 p) (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125478 n m p h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd p => @lem125477 n m p h0)). Qed.
Lemma lem125480 (m : nat) (p : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : (term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)).
Proof. exact (@lem125476 n m p (@lem125005 n h1)). Qed.
Lemma lem125481 (m : nat) (p : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)).
Proof. exact (@lem125479 n m p (@lem125004 n h1)). Qed.
Lemma lem125482 (m : nat) (p : nat) : (term64 m p) = ((term0 m) = (Coq.Arith.PeanoNat.Nat.Even p)).
Proof. exact (or_elim (@lem125003 (@el nat)) (fun h0 : Coq.Arith.PeanoNat.Nat.Even (@el nat) => @lem125481 m p (@el nat) h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd (@el nat) => @lem125480 m p (@el nat) h0)). Qed.
Lemma lem125487 (m : nat) : term71 m.
Proof. exact (fun p : nat => @lem125482 m p). Qed.
Lemma lem125488 (m : nat) (h1 : term16 m) : term20 m.
Proof. exact (EQ_MP (@lem125175 m h1) (@lem125487 m)). Qed.
Lemma lem125489 (m : nat) : term22 m.
Proof. exact (fun h0 : term16 m => @lem125488 m h0). Qed.
Lemma lem125494 : term26.
Proof. exact (fun m : nat => @lem125489 m). Qed.
Lemma lem125495 : term28.
Proof. exact (conj (@lem125098) (@lem125494)). Qed.
Lemma lem125496 : term33.
Proof. exact (@lem125028 (@lem125495)). Qed.
