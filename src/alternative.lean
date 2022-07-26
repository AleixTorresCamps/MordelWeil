import data.real.basic
import group_theory.finiteness
import algebra.group.defs

noncomputable theory

open set
open group
open subgroup
open add_group

-- Let G be a group and S the set of representants of G/mG
variables (G : Type*) [add_comm_group G]

def fin_quotient (S : set G) [finite S] (m : ℕ) := -- m ≥ 2
  ∀ g₀ : G, ∃ s ∈ S, ∃ g : G, g₀ = g + m•s

-- variables {S : set G} (hS_fin : finite S) (hS_ne : S.nonempty)

-- Heights formulated with a general m
structure height :=
-- (nonneg : ∀ g : G, 0 ≤ ht g)
(hfun : G → ℝ)
(C₁ : G → ℝ) (C₁_pos : ∀ g : G, 0 ≤ C₁ g)
(upper_bound : ∀ g₀ : G, ∀ g : G, hfun(g + g₀) ≤ 2*hfun g  + C₁ g₀)
(m : ℕ) (Hm : m ≥ 2)
(C₂ : ℝ) (C₂_pos : 0 ≤ C₂)
(lower_bound : ∀ g : G, hfun (m•g) ≥ (m^2)*(hfun g) - C₂)
(finite_boxes : ∀ C₃ : ℝ, {g : G | hfun g ≤ C₃}.finite)

-- variables {ht : G → ℝ} [height ht]
-- variables (hfinquot : fin_quotient S (height.m ht))

-- Needed lemma to define C
lemma Rnonempty {S : set G} (hS_fin : finite S)
 [fintype S] (hS : S.nonempty) {f : G → ℝ}: (f '' S).to_finset.nonempty :=
begin
obtain ⟨x, hx⟩ := hS,
use f x,
finish,
end

-- let C := max{C₁ Q | Q : S} + C₂
def C {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (ht.m)) : ℝ :=
  (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS)) + (ht.C₂)

-- variable {Cₛ : ℝ} [(C ht S.hs_ne h) Cₛ]   

-- 0 ≤ max{C₁ Q | Q : S}
lemma max_pos_is_pos  {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (ht.m)) :
  (0 : ℝ) ≤ (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS)) :=
begin
    let hS' := hS,
    obtain ⟨x, hx⟩ := hS,
    
    calc
    (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS')) ≥ ht.C₁ (-x) : by {
      apply finset.le_max',
      simp,
      use x,
      tauto,
    }
    ... ≥ 0 : ht.C₁_pos (-x),   
end

-- If s∈S, then C₁ -s ≤ C
lemma C₁S_le_C {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (ht.m))
(s : G) (hP : s ∈ S) : ht.C₁ (-s) ≤ (C G hS_fin ht hS h) :=
begin
  calc 
  (ht.C₁ (-s)) ≤ (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS)) : by {
    apply finset.le_max',
    simp,
    use s,
    tauto,
  }
  ... ≤ (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS)) + (ht.C₂) : 
    by linarith [ht.C₂_pos],
end

-- C₂ ≤ C
lemma C₂_le_C {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (height.m ht)) :
    (ht.C₂) ≤ (C G hS_fin ht hS h) :=
begin
  calc 
  (ht.C₂) ≤ (finset.max' ((λ s, ht.C₁ (-s)) '' S).to_finset (Rnonempty G hS_fin hS)) + (ht.C₂) :
    by linarith [max_pos_is_pos G hS_fin ht hS h],
end


-- This C has two important properties that combine C₁ and C₂

-- C₁
lemma useful_C {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S ht.m) (g g₀ : G) (hg₀ : g₀ ∈ S) :
(ht.hfun (g - g₀) ≤ 2*(ht.hfun g) + (C G hS_fin ht hS h))
:=
begin
  calc 
  ht.hfun (g - g₀) = ht.hfun (g + -g₀)       : by ring_nf
  ... ≤ 2*(ht.hfun g) + ht.C₁ (-g₀)          : ht.upper_bound (-g₀) g
  ... ≤ 2*(ht.hfun g) + (C G hS_fin ht hS h) : by linarith [C₁S_le_C G hS_fin ht hS h g₀ hg₀],
end

-- C₂
lemma useful_C' {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S ht.m) (g₀ : S) (g : G) :
(∀ g : G, ht.hfun (ht.m•g) ≥ ((ht.m)^2)*(ht.hfun g) - (C G hS_fin ht hS h))
:=
begin
  intro g,
  calc
  ht.hfun (ht.m•g) ≥ ((ht.m)^2)*(ht.hfun g) - ht.C₂    : ht.lower_bound g 
  ... ≥ ((ht.m)^2)*(ht.hfun g) - ht.C₂                 : by simp
  ... ≥ ((ht.m)^2)*(ht.hfun g) - (C G hS_fin ht hS h)  : by linarith [C₂_le_C G hS_fin ht hS h],
end

-- Set of generators: S ∪ {g : G | ht g ≤ C}
def U {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (height.m ht)) : set G :=
begin
  exact S ∪ {g : G | ht.hfun g ≤ (C G hS_fin ht hS h)},
end


def seq_P {S : set G} (hS_fin : finite S) (ht : height G)
(P : G) [fintype S] (hS : S.nonempty) (h : fin_quotient G S ht.m) : ℕ → G 
| 0 := P
| (n+1) := P
  -- Idea de la seqüencia:
  -- seq_P 0 = P
  -- seq_P succ n := el Q : G tal que seq_P n - Qₐ{iₙ} = mQ



-- Falta lemma diferents altures => diferents punts ?
-- Falten lemmes que reescriuen les desigualtats com s'utilitzen

lemma elem_with_height_less_C {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (height.m ht)) (P : G) 
(seq : ℕ → G) :
∃ (Pᵢ : G), ∃ (n : ℕ), (seq_P G hS_fin ht P hS h) n = Pᵢ ∧ ht.hfun Pᵢ ≤ (C G hS_fin ht hS h) :=
begin
  sorry

  -- Idea de la demo:
  -- Suposem el contrari
  -- Llavors per les desigualtats veiem que l'altura es va fent petita (altres lemmes?)
  -- Dir que tots els punts son diferents
  -- Dir que el conjunt de punts amb altura  ≤ ht P és infinit
  -- Arribem a contradicció 
end


-- Descent theorem
lemma main_theorem {S : set G} (hS_fin : finite S) (ht : height G)
[fintype S] (hS : S.nonempty) (h : fin_quotient G S (height.m ht)) : 
fg G :=
begin
  -- rw add_group.fg_iff,

  -- use S,
  -- split,

  -- Usar el lema usefull_C per obtenir la C
  -- Donar el subconjunt generador S ∪ {g : G | ht g ≤ C} (per propietats és finit)
  -- A partir d'aquí no entenc com funciona...
  -- Donat un P
  -- Definim la seq. {P_j} (amb les seves definicions/hipotesis) 
  -- Veiem que dins de la seq. hi ha elements d'altura ≤ C, diem-li Pⱼ
  -- S'ha d veure que podem escriure P com a combinació de Qᵢ i algun Pⱼ
  -- Ho usem pel Pⱼ que té altura ≤ C
  
  sorry
end
