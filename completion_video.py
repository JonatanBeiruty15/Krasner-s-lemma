from manim import *

class CompletionOfQ(Scene):
    def construct(self):
        base_y = 0
        lift_y = 1.2  # vertical shift for ℚ
        Q_color = RED

        # Step 1: Draw a white line for ℚ at base
        Q_line = Line(LEFT * 6, RIGHT * 6, color=WHITE)
        self.play(Create(Q_line))

        # Step 2: Add many red dots representing rationals
        num_rationals = 75
        rational_positions = [i / (num_rationals + 1) for i in range(1, num_rationals)]
        
        q_dots = VGroup(*[
            Dot(point=Q_line.point_from_proportion(p), color=Q_color, radius=0.1)
            for p in rational_positions
        ])
        self.play(FadeIn(q_dots, lag_ratio=0.02, run_time=2))
        self.wait(1)

        # ℚ Label (create it before moving)
        q_label = Text("ℚ", color=Q_color).next_to(Q_line, UP)

        # Step 3: Group line, dots, and label, then move up together
        q_group = VGroup(Q_line, q_dots, q_label)
        self.play(FadeIn(q_label), q_group.animate.shift(UP * lift_y))
        self.wait(1)

        # Step 4: Create the ℝ line
        R_line = Line(LEFT * 6, RIGHT * 6, color=Q_color)
        r_label = Text("ℝ", color=BLUE).next_to(R_line, DOWN)

        # TransformFromCopy from Q_line to R_line while keeping Q_group
        self.play(TransformFromCopy(Q_line, R_line), Write(r_label))
        self.wait(1)