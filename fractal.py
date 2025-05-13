from manim import *

class SierpinskiTriangleFractal(Scene):
    def construct(self):
        num_iterations = 4
        base_length = 6
        base_stroke_width = 6

        # STEP 1: Add Number Line at top
        axis = NumberLine(
            x_range=[-50, 50, 10],
            length=10,
            include_ticks=True,
            include_numbers=True,
            font_size=24,
        )
        axis.to_edge(UP)

        # Show only -50, 0, and 50 labels
        for number in axis.numbers:
            if int(number.get_value()) not in [-50, 0, 50]:
                number.set_opacity(0)

        self.play(Create(axis))
        self.wait()

        # STEP 2: Generate equilateral triangle
        A = LEFT * base_length / 2
        B = RIGHT * base_length / 2
        height = base_length * (3**0.5) / 2
        C = UP * height

        # Center and scale triangle
        centroid = (A + B + C) / 3
        translation_vector = -centroid + DOWN * 2  # Move it below the axis
        A += translation_vector
        B += translation_vector
        C += translation_vector

        initial_triangle = [A, B, C]

        base = Polygon(*initial_triangle, color=WHITE, stroke_width=base_stroke_width)
        base.scale(0.6)  # Make triangle smaller
        self.play(Create(base))
        self.wait()

        triangle_levels = [[base]]

        # STEP 3: Generate fractal
        for order in range(1, num_iterations + 1):
            new_triangles = []

            for tri in triangle_levels[order - 1]:
                A, B, C = tri.get_vertices()
                AB = interpolate(A, B, 0.5)
                BC = interpolate(B, C, 0.5)
                CA = interpolate(C, A, 0.5)

                stroke = base_stroke_width * (0.6 ** order)
                t1 = Polygon(A, AB, CA, color=RED, stroke_width=stroke)
                t2 = Polygon(AB, B, BC, color=RED, stroke_width=stroke)
                t3 = Polygon(CA, BC, C, color=RED, stroke_width=stroke)

                new_triangles.extend([t1, t2, t3])

            triangle_levels.append(new_triangles)

            self.play(
                LaggedStartMap(Create, VGroup(*new_triangles), lag_ratio=0.05),
                run_time=2
            )

            self.play(
                *[tri.animate.set_color(WHITE) for tri in new_triangles],
                run_time=1
            )

            self.wait(0.3)

        self.wait()