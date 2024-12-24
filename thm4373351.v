Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4373351_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464394_spec.
Require Import thm3464397_spec.
Lemma lem4373023 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4373024 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4373025 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4373024 _103718 _103721 x) (@lem4373023 _103718 _103721 x)). Qed.
Lemma lem4373026 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4373025 _103718 _103721 x y). Qed.
Lemma lem4373027 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4373028 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4373027 _103718 _103721 x y) (@lem4373026 _103718 _103721 x y)). Qed.
Lemma lem4373029 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4373028 _103718 _103721 x y s). Qed.
Lemma lem4373030 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4373031 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4373030 _103718 _103721 x s y) (@lem4373029 _103718 _103721 x y s)). Qed.
Lemma lem4373032 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4373031 _103718 _103721 x s y t). Qed.
Lemma lem4373033 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4373059 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4373060 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem4373059 _83095 p). Qed.
Lemma lem4373061 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem4373062 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem4373061 _83095 p) (@lem4373060 _83095 p)). Qed.
Lemma lem4373063 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem4373062 _83095 p x). Qed.
Lemma lem4373064 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem4373073 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4373074 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem4373076 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4373077 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4373078 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4373077 A s) (@lem4373076 A s)). Qed.
Lemma lem4373079 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4373078 A s t). Qed.
Lemma lem4373080 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4373090 {_89769 _89788 _89789 : Type'} : term21 _89769 _89788 _89789.
Proof. exact (EQ_MP (@lem3464397 _89769 _89788 _89789) (@lem3464394 _89769 _89788 _89789)). Qed.
Lemma lem4373091 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : term22 _89769 _89788 _89789 P.
Proof. exact (@lem4373090 _89769 _89788 _89789 P). Qed.
Lemma lem4373092 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : (term22 _89769 _89788 _89789 P) = (term23 _89769 _89788 _89789 P).
Proof. exact (eq_refl (term22 _89769 _89788 _89789 P)). Qed.
Lemma lem4373093 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) : term23 _89769 _89788 _89789 P.
Proof. exact (EQ_MP (@lem4373092 _89769 _89788 _89789 P) (@lem4373091 _89769 _89788 _89789 P)). Qed.
Lemma lem4373094 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term24 _89769 _89788 _89789 P f.
Proof. exact (@lem4373093 _89769 _89788 _89789 P f). Qed.
Lemma lem4373095 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term24 _89769 _89788 _89789 P f) = ((term25 _89769 _89788 _89789 P f) = (term26 _89769 _89788 _89789 P f)).
Proof. exact (eq_refl (term24 _89769 _89788 _89789 P f)). Qed.
Lemma lem4373133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4373080 A s t) (@lem4373079 A s t)). Qed.
Lemma lem4373134 {_104907 _104908 : Type'} (s : type1210 _104907 _104908) (t : type1210 _104907 _104908) : (s = t) = (term27 _104907 _104908 s t).
Proof. exact (@lem4373133 (prod _104907 _104908) s t). Qed.
Lemma lem4373135 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f g)) = (term30 _104907 _104908 f g).
Proof. exact (@lem4373134 _104907 _104908 (term28 _104907 _104908 f g) (term29 _104907 _104908 f g)). Qed.
Lemma lem4373141 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4373074 _5106 _5107 P) (@lem4373073 _5106 _5107 P)). Qed.
Lemma lem4373142 {_104907 _104908 : Type'} (P : type1210 _104907 _104908) : (term31 _104907 _104908 P) = (term32 _104907 _104908 P).
Proof. exact (@lem4373141 _104908 _104907 P). Qed.
Lemma lem4373143 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term33 _104907 _104908 f g) = (term34 _104907 _104908 f g).
Proof. exact (@lem4373142 _104907 _104908 (term35 _104907 _104908 f g)). Qed.
Lemma lem4373144 {_104907 _104908 : Type'} (x : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term36 _104907 _104908 f g x) = ((term37 _104907 _104908 x f g) = (term38 _104907 _104908 x f g)).
Proof. exact (eq_refl (term36 _104907 _104908 f g x)). Qed.
Lemma lem4373145 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term39 _104907 _104908 f g) = (term35 _104907 _104908 f g).
Proof. exact (fun_ext (fun x : prod _104907 _104908 => @lem4373144 _104907 _104908 x f g)). Qed.
Lemma lem4373146 {_104907 _104908 : Type'} : (@all (prod _104907 _104908)) = (@all (prod _104907 _104908)).
Proof. exact (eq_refl (@all (prod _104907 _104908))). Qed.
Lemma lem4373147 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term33 _104907 _104908 f g) = (term30 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373146 _104907 _104908) (@lem4373145 _104907 _104908 f g)). Qed.
Lemma lem4373148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373149 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term40 _104907 _104908 f g) = (term41 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373148) (@lem4373147 _104907 _104908 f g)). Qed.
Lemma lem4373150 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) (g : type686 _104908) : (term42 _104907 _104908 f g p1 p2) = ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 f g)).
Proof. exact (eq_refl (term42 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373151 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) : (term45 _104907 _104908 f g p1) = (term46 _104907 _104908 p1 f g).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4373150 _104907 _104908 p1 p2 f g)). Qed.
Lemma lem4373152 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4373153 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) : (term47 _104907 _104908 f g p1) = (term48 _104907 _104908 p1 f g).
Proof. exact (MK_COMB (@lem4373152 _104908) (@lem4373151 _104907 _104908 p1 f g)). Qed.
Lemma lem4373154 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term49 _104907 _104908 f g) = (term50 _104907 _104908 f g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4373153 _104907 _104908 p1 f g)). Qed.
Lemma lem4373155 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4373156 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term34 _104907 _104908 f g) = (term51 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373155 _104907) (@lem4373154 _104907 _104908 f g)). Qed.
Lemma lem4373157 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term33 _104907 _104908 f g) = (term34 _104907 _104908 f g)) = ((term30 _104907 _104908 f g) = (term51 _104907 _104908 f g)).
Proof. exact (MK_COMB (@lem4373149 _104907 _104908 f g) (@lem4373156 _104907 _104908 f g)). Qed.
Lemma lem4373158 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term30 _104907 _104908 f g) = (term51 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4373157 _104907 _104908 f g) (@lem4373143 _104907 _104908 f g)). Qed.
Lemma lem4373165 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f g)) = (term51 _104907 _104908 f g).
Proof. exact (TRANS (@lem4373135 _104907 _104908 f g) (@lem4373158 _104907 _104908 f g)). Qed.
Lemma lem4373177 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373033 _103718 _103721 x s y t) (@lem4373032 _103718 _103721 x s y t)). Qed.
Lemma lem4373178 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4373177 _104907 _104908 x s y t). Qed.
Lemma lem4373179 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) : (term43 _104907 _104908 p1 p2 f g) = (term52 _104907 _104908 p1 f p2 g).
Proof. exact (@lem4373178 _104907 _104908 p1 (@INTERS _104907 f) p2 (@INTERS _104908 g)). Qed.
Lemma lem4373182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373183 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (p2 : _104908) (g : type686 _104908) : (term53 _104907 _104908 p1 p2 f g) = (term54 _104907 _104908 p1 f p2 g).
Proof. exact (MK_COMB (@lem4373182) (@lem4373179 _104907 _104908 p1 f p2 g)). Qed.
Lemma lem4373185 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term25 _89769 _89788 _89789 P f) = (term26 _89769 _89788 _89789 P f).
Proof. exact (EQ_MP (@lem4373095 _89769 _89788 _89789 P f) (@lem4373094 _89769 _89788 _89789 P f)). Qed.
Lemma lem4373186 {_104907 _104908 : Type'} (P : type658 _104907 _104908) (f : type654 _104907 _104908) : (term55 _104907 _104908 P f) = (term56 _104907 _104908 P f).
Proof. exact (@lem4373185 (prod _104907 _104908) (_104908 -> Prop) (_104907 -> Prop) P f). Qed.
Lemma lem4373187 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term57 _104907 _104908 f g) = (term58 _104907 _104908 f g).
Proof. exact (@lem4373186 _104907 _104908 (term59 _104907 _104908 f g) (@CROSS _104908 _104907)). Qed.
Lemma lem4373188 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) : (term60 _104907 _104908 f g s) = (term61 _104907 _104908 s f g).
Proof. exact (eq_refl (term60 _104907 _104908 f g s)). Qed.
Lemma lem4373189 {_104908 : Type'} (t : _104908 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4373190 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (t : _104908 -> Prop) : (term62 _104907 _104908 f g s t) = (term63 _104907 _104908 s f g t).
Proof. exact (MK_COMB (@lem4373188 _104907 _104908 s f g) (@lem4373189 _104908 t)). Qed.
Lemma lem4373191 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term63 _104907 _104908 s f g t) = (term64 _104907 _104908 s f t g).
Proof. exact (eq_refl (term63 _104907 _104908 s f g t)). Qed.
Lemma lem4373192 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term62 _104907 _104908 f g s t) = (term64 _104907 _104908 s f t g).
Proof. exact (TRANS (@lem4373190 _104907 _104908 s f g t) (@lem4373191 _104907 _104908 s f t g)). Qed.
Lemma lem4373193 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) : (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_136) = (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_136).
Proof. exact (eq_refl (@SETSPEC ((prod _104907 _104908) -> Prop) GEN_PVAR_136)). Qed.
Lemma lem4373194 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term65 _104907 _104908 GEN_PVAR_136 f g s t) = (term66 _104907 _104908 GEN_PVAR_136 s f t g).
Proof. exact (MK_COMB (@lem4373193 _104907 _104908 GEN_PVAR_136) (@lem4373192 _104907 _104908 s f t g)). Qed.
Lemma lem4373195 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) : (@CROSS _104908 _104907 s t) = (@CROSS _104908 _104907 s t).
Proof. exact (eq_refl (@CROSS _104908 _104907 s t)). Qed.
Lemma lem4373196 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (t : _104908 -> Prop) : (term67 _104907 _104908 GEN_PVAR_136 f g s t) = (term68 _104907 _104908 GEN_PVAR_136 f g s t).
Proof. exact (MK_COMB (@lem4373194 _104907 _104908 GEN_PVAR_136 s f t g) (@lem4373195 _104907 _104908 s t)). Qed.
Lemma lem4373197 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) : (term69 _104907 _104908 GEN_PVAR_136 f g s) = (term70 _104907 _104908 GEN_PVAR_136 f g s).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4373196 _104907 _104908 GEN_PVAR_136 f g s t)). Qed.
Lemma lem4373198 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4373199 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) : (term71 _104907 _104908 GEN_PVAR_136 f g s) = (term72 _104907 _104908 GEN_PVAR_136 f g s).
Proof. exact (MK_COMB (@lem4373198 _104908) (@lem4373197 _104907 _104908 GEN_PVAR_136 f g s)). Qed.
Lemma lem4373200 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term73 _104907 _104908 GEN_PVAR_136 f g) = (term74 _104907 _104908 GEN_PVAR_136 f g).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4373199 _104907 _104908 GEN_PVAR_136 f g s)). Qed.
Lemma lem4373201 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4373202 {_104907 _104908 : Type'} (GEN_PVAR_136 : type1210 _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term75 _104907 _104908 GEN_PVAR_136 f g) = (term76 _104907 _104908 GEN_PVAR_136 f g).
Proof. exact (MK_COMB (@lem4373201 _104907) (@lem4373200 _104907 _104908 GEN_PVAR_136 f g)). Qed.
Lemma lem4373203 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term77 _104907 _104908 f g) = (term78 _104907 _104908 f g).
Proof. exact (fun_ext (fun GEN_PVAR_136 : type1210 _104907 _104908 => @lem4373202 _104907 _104908 GEN_PVAR_136 f g)). Qed.
Lemma lem4373204 {_104907 _104908 : Type'} : (@GSPEC ((prod _104907 _104908) -> Prop)) = (@GSPEC ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4373205 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term79 _104907 _104908 f g) = (term80 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373204 _104907 _104908) (@lem4373203 _104907 _104908 f g)). Qed.
Lemma lem4373206 {_104907 _104908 : Type'} : (@INTERS (prod _104907 _104908)) = (@INTERS (prod _104907 _104908)).
Proof. exact (eq_refl (@INTERS (prod _104907 _104908))). Qed.
Lemma lem4373207 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term57 _104907 _104908 f g) = (term29 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373206 _104907 _104908) (@lem4373205 _104907 _104908 f g)). Qed.
Lemma lem4373208 {_104907 _104908 : Type'} : (@eq ((prod _104907 _104908) -> Prop)) = (@eq ((prod _104907 _104908) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104907 _104908) -> Prop))). Qed.
Lemma lem4373209 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term81 _104907 _104908 f g) = (term82 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373208 _104907 _104908) (@lem4373207 _104907 _104908 f g)). Qed.
Lemma lem4373210 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) : (term60 _104907 _104908 f g s) = (term61 _104907 _104908 s f g).
Proof. exact (eq_refl (term60 _104907 _104908 f g s)). Qed.
Lemma lem4373211 {_104908 : Type'} (t : _104908 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4373212 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (t : _104908 -> Prop) : (term62 _104907 _104908 f g s t) = (term63 _104907 _104908 s f g t).
Proof. exact (MK_COMB (@lem4373210 _104907 _104908 s f g) (@lem4373211 _104908 t)). Qed.
Lemma lem4373213 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term63 _104907 _104908 s f g t) = (term64 _104907 _104908 s f t g).
Proof. exact (eq_refl (term63 _104907 _104908 s f g t)). Qed.
Lemma lem4373214 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term62 _104907 _104908 f g s t) = (term64 _104907 _104908 s f t g).
Proof. exact (TRANS (@lem4373212 _104907 _104908 s f g t) (@lem4373213 _104907 _104908 s f t g)). Qed.
Lemma lem4373215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4373216 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term83 _104907 _104908 f g s t) = (term84 _104907 _104908 s f t g).
Proof. exact (MK_COMB (@lem4373215) (@lem4373214 _104907 _104908 s f t g)). Qed.
Lemma lem4373217 {_104907 _104908 : Type'} (a : prod _104907 _104908) (s : _104907 -> Prop) (t : _104908 -> Prop) : (term85 _104907 _104908 a s t) = (term85 _104907 _104908 a s t).
Proof. exact (eq_refl (term85 _104907 _104908 a s t)). Qed.
Lemma lem4373218 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) (s : _104907 -> Prop) (t : _104908 -> Prop) : (term86 _104907 _104908 f g a s t) = (term87 _104907 _104908 f g a s t).
Proof. exact (MK_COMB (@lem4373216 _104907 _104908 s f t g) (@lem4373217 _104907 _104908 a s t)). Qed.
Lemma lem4373219 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) (s : _104907 -> Prop) : (term88 _104907 _104908 f g a s) = (term89 _104907 _104908 f g a s).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4373218 _104907 _104908 f g a s t)). Qed.
Lemma lem4373220 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4373221 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) (s : _104907 -> Prop) : (term90 _104907 _104908 f g a s) = (term91 _104907 _104908 f g a s).
Proof. exact (MK_COMB (@lem4373220 _104908) (@lem4373219 _104907 _104908 f g a s)). Qed.
Lemma lem4373222 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term92 _104907 _104908 f g a) = (term93 _104907 _104908 f g a).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4373221 _104907 _104908 f g a s)). Qed.
Lemma lem4373223 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4373224 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term94 _104907 _104908 f g a) = (term95 _104907 _104908 f g a).
Proof. exact (MK_COMB (@lem4373223 _104907) (@lem4373222 _104907 _104908 f g a)). Qed.
Lemma lem4373225 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_58) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_58).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_58)). Qed.
Lemma lem4373226 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term96 _104907 _104908 GEN_PVAR_58 f g a) = (term97 _104907 _104908 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem4373225 _104907 _104908 GEN_PVAR_58) (@lem4373224 _104907 _104908 f g a)). Qed.
Lemma lem4373227 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4373228 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term98 _104907 _104908 GEN_PVAR_58 f g a) = (term99 _104907 _104908 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem4373226 _104907 _104908 GEN_PVAR_58 f g a) (@lem4373227 _104907 _104908 a)). Qed.
Lemma lem4373229 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term100 _104907 _104908 GEN_PVAR_58 f g) = (term101 _104907 _104908 GEN_PVAR_58 f g).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4373228 _104907 _104908 GEN_PVAR_58 f g a)). Qed.
Lemma lem4373230 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4373231 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term102 _104907 _104908 GEN_PVAR_58 f g) = (term103 _104907 _104908 GEN_PVAR_58 f g).
Proof. exact (MK_COMB (@lem4373230 _104907 _104908) (@lem4373229 _104907 _104908 GEN_PVAR_58 f g)). Qed.
Lemma lem4373232 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term104 _104907 _104908 f g) = (term105 _104907 _104908 f g).
Proof. exact (fun_ext (fun GEN_PVAR_58 : prod _104907 _104908 => @lem4373231 _104907 _104908 GEN_PVAR_58 f g)). Qed.
Lemma lem4373233 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4373234 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term58 _104907 _104908 f g) = (term106 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373233 _104907 _104908) (@lem4373232 _104907 _104908 f g)). Qed.
Lemma lem4373235 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term57 _104907 _104908 f g) = (term58 _104907 _104908 f g)) = ((term29 _104907 _104908 f g) = (term106 _104907 _104908 f g)).
Proof. exact (MK_COMB (@lem4373209 _104907 _104908 f g) (@lem4373234 _104907 _104908 f g)). Qed.
Lemma lem4373236 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term29 _104907 _104908 f g) = (term106 _104907 _104908 f g).
Proof. exact (EQ_MP (@lem4373235 _104907 _104908 f g) (@lem4373187 _104907 _104908 f g)). Qed.
Lemma lem4373257 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term107 _104907 _104908 p1 p2) = (term107 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term107 _104907 _104908 p1 p2)). Qed.
Lemma lem4373258 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) (g : type686 _104908) : (term44 _104907 _104908 p1 p2 f g) = (term108 _104907 _104908 p1 p2 f g).
Proof. exact (MK_COMB (@lem4373257 _104907 _104908 p1 p2) (@lem4373236 _104907 _104908 f g)). Qed.
Lemma lem4373260 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4373064 _83095 p x) (@lem4373063 _83095 p x)). Qed.
Lemma lem4373261 {_104907 _104908 : Type'} (p : type1210 _104907 _104908) (x : prod _104907 _104908) : (term109 _104907 _104908 x p) = (p x).
Proof. exact (@lem4373260 (prod _104907 _104908) p x). Qed.
Lemma lem4373262 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term110 _104907 _104908 p1 p2 f g) = (term111 _104907 _104908 f g p1 p2).
Proof. exact (@lem4373261 _104907 _104908 (term112 _104907 _104908 f g) (@pair _104907 _104908 p1 p2)). Qed.
Lemma lem4373263 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term113 _104907 _104908 f g a) = (term95 _104907 _104908 f g a).
Proof. exact (eq_refl (term113 _104907 _104908 f g a)). Qed.
Lemma lem4373264 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) : (@SETSPEC (prod _104907 _104908) GEN_PVAR_58) = (@SETSPEC (prod _104907 _104908) GEN_PVAR_58).
Proof. exact (eq_refl (@SETSPEC (prod _104907 _104908) GEN_PVAR_58)). Qed.
Lemma lem4373265 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term114 _104907 _104908 GEN_PVAR_58 f g a) = (term97 _104907 _104908 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem4373264 _104907 _104908 GEN_PVAR_58) (@lem4373263 _104907 _104908 f g a)). Qed.
Lemma lem4373266 {_104907 _104908 : Type'} (a : prod _104907 _104908) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4373267 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) (a : prod _104907 _104908) : (term115 _104907 _104908 GEN_PVAR_58 f g a) = (term99 _104907 _104908 GEN_PVAR_58 f g a).
Proof. exact (MK_COMB (@lem4373265 _104907 _104908 GEN_PVAR_58 f g a) (@lem4373266 _104907 _104908 a)). Qed.
Lemma lem4373268 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term116 _104907 _104908 GEN_PVAR_58 f g) = (term101 _104907 _104908 GEN_PVAR_58 f g).
Proof. exact (fun_ext (fun a : prod _104907 _104908 => @lem4373267 _104907 _104908 GEN_PVAR_58 f g a)). Qed.
Lemma lem4373269 {_104907 _104908 : Type'} : (@ex (prod _104907 _104908)) = (@ex (prod _104907 _104908)).
Proof. exact (eq_refl (@ex (prod _104907 _104908))). Qed.
Lemma lem4373270 {_104907 _104908 : Type'} (GEN_PVAR_58 : prod _104907 _104908) (f : type686 _104907) (g : type686 _104908) : (term117 _104907 _104908 GEN_PVAR_58 f g) = (term103 _104907 _104908 GEN_PVAR_58 f g).
Proof. exact (MK_COMB (@lem4373269 _104907 _104908) (@lem4373268 _104907 _104908 GEN_PVAR_58 f g)). Qed.
Lemma lem4373271 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term118 _104907 _104908 f g) = (term105 _104907 _104908 f g).
Proof. exact (fun_ext (fun GEN_PVAR_58 : prod _104907 _104908 => @lem4373270 _104907 _104908 GEN_PVAR_58 f g)). Qed.
Lemma lem4373272 {_104907 _104908 : Type'} : (@GSPEC (prod _104907 _104908)) = (@GSPEC (prod _104907 _104908)).
Proof. exact (eq_refl (@GSPEC (prod _104907 _104908))). Qed.
Lemma lem4373273 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term119 _104907 _104908 f g) = (term106 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373272 _104907 _104908) (@lem4373271 _104907 _104908 f g)). Qed.
Lemma lem4373274 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) : (term107 _104907 _104908 p1 p2) = (term107 _104907 _104908 p1 p2).
Proof. exact (eq_refl (term107 _104907 _104908 p1 p2)). Qed.
Lemma lem4373275 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) (g : type686 _104908) : (term110 _104907 _104908 p1 p2 f g) = (term108 _104907 _104908 p1 p2 f g).
Proof. exact (MK_COMB (@lem4373274 _104907 _104908 p1 p2) (@lem4373273 _104907 _104908 f g)). Qed.
Lemma lem4373276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4373277 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (f : type686 _104907) (g : type686 _104908) : (term120 _104907 _104908 p1 p2 f g) = (term121 _104907 _104908 p1 p2 f g).
Proof. exact (MK_COMB (@lem4373276) (@lem4373275 _104907 _104908 p1 p2 f g)). Qed.
Lemma lem4373278 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term111 _104907 _104908 f g p1 p2) = (term122 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term111 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373279 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term110 _104907 _104908 p1 p2 f g) = (term111 _104907 _104908 f g p1 p2)) = ((term108 _104907 _104908 p1 p2 f g) = (term122 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4373277 _104907 _104908 p1 p2 f g) (@lem4373278 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373280 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term108 _104907 _104908 p1 p2 f g) = (term122 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4373279 _104907 _104908 f g p1 p2) (@lem4373262 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373298 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4373033 _103718 _103721 x s y t) (@lem4373032 _103718 _103721 x s y t)). Qed.
Lemma lem4373299 {_104907 _104908 : Type'} (x : _104907) (s : _104907 -> Prop) (y : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 x y s t) = (term8 _104907 _104908 x s y t).
Proof. exact (@lem4373298 _104907 _104908 x s y t). Qed.
Lemma lem4373300 {_104907 _104908 : Type'} (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) (t : _104908 -> Prop) : (term7 _104907 _104908 p1 p2 s t) = (term8 _104907 _104908 p1 s p2 t).
Proof. exact (@lem4373299 _104907 _104908 p1 s p2 t). Qed.
Lemma lem4373303 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (t : _104908 -> Prop) (g : type686 _104908) : (term84 _104907 _104908 s f t g) = (term84 _104907 _104908 s f t g).
Proof. exact (eq_refl (term84 _104907 _104908 s f t g)). Qed.
Lemma lem4373304 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) (t : _104908 -> Prop) : (term123 _104907 _104908 f g p1 p2 s t) = (term124 _104907 _104908 f g p1 s p2 t).
Proof. exact (MK_COMB (@lem4373303 _104907 _104908 s f t g) (@lem4373300 _104907 _104908 p1 s p2 t)). Qed.
Lemma lem4373307 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) : (term125 _104907 _104908 f g p1 p2 s) = (term126 _104907 _104908 f g p1 s p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4373304 _104907 _104908 f g p1 s p2 t)). Qed.
Lemma lem4373308 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4373309 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (s : _104907 -> Prop) (p2 : _104908) : (term127 _104907 _104908 f g p1 p2 s) = (term128 _104907 _104908 f g p1 s p2).
Proof. exact (MK_COMB (@lem4373308 _104908) (@lem4373307 _104907 _104908 f g p1 s p2)). Qed.
Lemma lem4373316 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term129 _104907 _104908 f g p1 p2) = (term130 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4373309 _104907 _104908 f g p1 s p2)). Qed.
Lemma lem4373317 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4373318 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term122 _104907 _104908 f g p1 p2) = (term131 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4373317 _104907) (@lem4373316 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373325 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term108 _104907 _104908 p1 p2 f g) = (term131 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4373280 _104907 _104908 f g p1 p2) (@lem4373318 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373326 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term44 _104907 _104908 p1 p2 f g) = (term131 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4373258 _104907 _104908 p1 p2 f g) (@lem4373325 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373327 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term43 _104907 _104908 p1 p2 f g) = (term44 _104907 _104908 p1 p2 f g)) = ((term52 _104907 _104908 p1 f p2 g) = (term131 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4373183 _104907 _104908 p1 f p2 g) (@lem4373326 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373332 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term46 _104907 _104908 p1 f g) = (term132 _104907 _104908 f g p1).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4373327 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4373333 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4373334 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term48 _104907 _104908 p1 f g) = (term133 _104907 _104908 f g p1).
Proof. exact (MK_COMB (@lem4373333 _104908) (@lem4373332 _104907 _104908 f g p1)). Qed.
Lemma lem4373341 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term50 _104907 _104908 f g) = (term134 _104907 _104908 f g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4373334 _104907 _104908 f g p1)). Qed.
Lemma lem4373342 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4373343 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term51 _104907 _104908 f g) = (term135 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4373342 _104907) (@lem4373341 _104907 _104908 f g)). Qed.
Lemma lem4373350 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f g)) = (term135 _104907 _104908 f g).
Proof. exact (TRANS (@lem4373165 _104907 _104908 f g) (@lem4373343 _104907 _104908 f g)). Qed.
Lemma lem4373351 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term135 _104907 _104908 f g) = ((term28 _104907 _104908 f g) = (term29 _104907 _104908 f g)).
Proof. exact (SYM (@lem4373350 _104907 _104908 f g)). Qed.
