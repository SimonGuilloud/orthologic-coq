#!/usr/bin/env python3

import argparse
import re
from typing import Any, Callable, Tuple
from pathlib import Path
from dataclasses import dataclass

import seaborn as sns
from matplotlib import pyplot as plt
import numpy as np
import pandas as pd

BENCHMARK_ENTRY = re.compile(
    r"""::[ ]"(?P<experiment>.*?)"[ ]:::[ ]"?(?P<solver>.*?)"?[ ]:::[ ]"?(?P<reduction>.*?)"?[\n]
        (?:Goals[ ]left:[ ](?P<numgoals>[0-9]+)[\n])?
        (?:(?P<timeout>timeout)[\n])?
        Tactic[ ]call[ ]ran[ ]for[ ](?P<wall>.*?)[ ]secs[ ][(](?P<user>.*?)u,(?P<system>.*?)s[)]""",
    re.VERBOSE
)

SEPARATOR = "-" * 80 + "\n"

def parse_entry(entry_contents: str) -> dict[str, Any]:
    if m := BENCHMARK_ENTRY.match(entry_contents):
        d = m.groupdict()
        timeout, numgoals = d.pop("timeout"), d.pop("numgoals")
        d["status"] = timeout or ("solved" if numgoals == "0" else "not solved")
        return d
    # assert m, f"Unparseable entry: {entry_contents}"
    return None

SOLVER_RENAME = {
    "btauto": "btauto",

    "OL_Reflection_1_base.reduce_to_decideOL": "OL",
    "OL_Reflection_2_opti.reduce_to_decideOL_opti": "OL+o",
    "OL_Reflection_3_memo.reduce_to_decideOL_memo": "OL+o+l",
    "OL_Reflection_4_fmap.reduce_to_decideOL_fmap": "OL+o+m",
    "OL_Reflection_5_pointers.reduce_to_decideOL_pointer": "OL+o+m+φ",
    "oltauto": "OLT",
    "olcert_goal": "OCaml",
    "oltauto_cert": "OCaml+n",
}

SOLVER_RENAME_OLD = {
    # Old names
    "OL_Reflection_2_memo.reduce_to_decideOL_memo": "OL+l",
    "OL_Reflection_3_fmap.reduce_to_decideOL_fmap": "OL+m",
    "OL_Reflection_4_pointers.reduce_to_decideOL_pointer": "OL+m+φ",
    # Older names
    "OL_Reflection_1_base.reduceToAlgo": "OL",
    "OL_Reflection_2_memo.reduceToAlgoMemo": "OL+l",
    "OL_Reflection_3_fmap.reduceToAlgoFmap": "OL+m",
    "OL_Reflection_4_pointers.reduceToAlgoPointers": "OL+m+φ",
}

REDUCTION_RENAME = {
    "lazy": "+lz",
    "compute": "+c",
    "vm_compute": "+vm",
    "none": "",
}

def parse_log(contents: str) -> pd.DataFrame:
    df = pd.DataFrame(
        entry for entry_contents in contents.split(SEPARATOR)
        if entry_contents.strip()
        if (entry := parse_entry(entry_contents))
    )
    if df.empty:
        return df
    df["solver"] = df["solver"].map(SOLVER_RENAME | SOLVER_RENAME_OLD) # type: ignore
    df["solver+reduction"] = df["solver"] + df["reduction"].map(REDUCTION_RENAME) # type: ignore
    if df.experiment.str.contains("_").any():
        df[["experiment", "variation"]] = df["experiment"].str.split("_(?=[0-9])", n=1, expand=True)
    else:
        df["variation"] = 1
    df[["experiment", "size"]] = df["experiment"].str.split("(?=[0-9])", n=1, expand=True)
    df["size"] = pd.to_numeric(df["size"])
    df["wall"] = pd.to_numeric(df["wall"])
    df["user"] = pd.to_numeric(df["user"])
    df["system"] = pd.to_numeric(df["system"])
    # print(df)
    return df

def parse_logs(contents: list[str]) -> pd.DataFrame:
    return pd.concat(parse_log(l) for l in contents)

def plot_lines(df):
    plt.figure(figsize=(6, 4))

    # df = df[df["reduction"].isin(("btauto", "vm_compute"))]
    # df = df[df["status"] == "solved"]
    # ax = sns.violinplot(
    # ax = sns.barplot(errorbar="ci",
    solvers, reductions = df["solver"].unique(), df["reduction"].unique()
    solvers = [r for r in SOLVER_RENAME.values() if r in solvers]
    reductions = [r for r in REDUCTION_RENAME if r in reductions]
    ax = sns.lineplot(
        marker="o",
        data=df, x="size", y="wall",
        hue="solver", hue_order=["OL", "OL+o", "btauto", "OL+o+l", "OL+o+m", "OL+o+m+φ", "OCaml"],
        style="reduction", style_order=reductions,
    )

    # ax.set_yscale('log')
    ax.set_xlim(0, 100)
    ax.set_ylim(0, 28)

    # plt.xticks(rotation=45, ha='right')
    # plt.title('Wall time')
    plt.xlabel('Formula size')
    plt.ylabel('Wall clock time (seconds)')
    # plt.legend(title='Solver')
    plt.tight_layout()

    plt.legend(loc = 'upper right')
    plt.savefig("lines.pdf")
    plt.show()
    return

def plot_cloud(df):
    solvers = df["solver"].unique()
    df = df[["solver", "variation", "size", "wall"]]
    df = df.groupby(["size", "variation", "solver"])[["wall"]].mean().unstack().reset_index()
    df = df.droplevel(axis=1, level=0)
    for s1 in solvers:
        for s2 in solvers:
            if s1 >= s2:
                continue
            print(s1, s2)
            sns.scatterplot(data=df, x=s1, y=s2)
            plt.savefig(f"{s1}+{s2}.pdf")
            plt.show()

def parse_arguments():
    parser = argparse.ArgumentParser(description='Plot Coq-OL benchmark results.')
    parser.add_argument("style", choices=["cloud", "lines"])
    parser.add_argument("infile", nargs='+', type=Path,
                        help="File to read benchmarks from.")
    return parser.parse_args()

@dataclass
class Fit:
    label: str
    xdata: Any
    ydata: Any
    fn: Any
    fn_str: Callable[..., str]
    bounds: tuple[Any, ...]

    def __post_init__(self):
        from scipy.optimize import curve_fit
        from sklearn.metrics import r2_score

        self.popt, self.pcov = curve_fit(self.fn, self.xdata, self.ydata, bounds=self.bounds)
        self.y_pred = self.fn(self.xdata, *self.popt)
        self.r2 = r2_score(self.ydata, self.y_pred)
        self.cond = np.linalg.cond(self.pcov)

    @property
    def descr(self):
        return self.fn_str(*self.popt)

    @property
    def title(self):
        return f"{self.label} ≈ {self.descr}: r2={self.r2:.3f}, cond={self.cond:.2g}"

    def plot(self):
        ax = sns.lineplot(
            marker="o",
            data=(pd
                  .DataFrame({"size": self.xdata, self.label: self.ydata, self.descr: self.y_pred})
                  .melt('size', var_name='kind', value_name='wall')),
            x='size', y='wall', hue='kind')
        plt.title(self.title)
        plt.show()

class PolyFit(Fit):
    def __init__(self, label: str, xdata, ydata, n):
        fn = lambda x, a, b: a * x**n + b
        fn_str = lambda a, b: f"{a:.2g} * x**{n} + {b:.2g}"
        bounds = ((0, 0), (np.inf, np.inf))
        super().__init__(label, xdata, ydata, fn, fn_str, bounds)

class PolyFullFit(Fit):
    def __init__(self, label: str, xdata, ydata):
        fn = lambda x, a, b, c: a * x**b + c
        fn_str = lambda a, b, c: f"{a:.2g} * x**{b:.2g} + {c:.2g}"
        bounds = ((0, 0, 0), (np.inf, np.inf, np.inf))
        super().__init__(label, xdata, ydata, fn, fn_str, bounds)

class PolyLogFit(Fit):
    def __init__(self, label: str, xdata, ydata, n, nlog):
        fn = lambda x, a, b: a * x**n * np.log2(x)**nlog + b
        fn_str = lambda a, b: f"{a:.2g} * x**{n} * np.log2(x)**{nlog} + {b:.2g}"
        bounds = ((0, 0), (np.inf, np.inf))
        super().__init__(label, xdata, ydata, fn, fn_str, bounds)

class ExpFit(Fit):
    def __init__(self, label: str, xdata, ydata):
        fn = lambda x, a, b, c: a * np.exp(b * x) + c
        fn_str = lambda a, b, c: f"{a:.2g} * np.exp({b:.2g} * x) + {c:.2g}"
        bounds = ((0, 0, 0), (np.inf, np.inf, np.inf))
        super().__init__(label, xdata, ydata, fn, fn_str, bounds)

def fit(df):
    df = df[df["wall"] < 20] # Remove timeouts
    stats = df.groupby(["solver+reduction", "size"])[["wall"]].agg(("mean", "std"))
    for (algorithm, plot) in sorted(stats.groupby("solver+reduction")):
        plot = plot.reset_index()
        # print(plot.reset_index())
        # print(plot.reset_index().columns)
        xdata, ydata, sigma = plot["size"], plot[("wall", "mean")], plot[("wall", "std")]

        if len(ydata) < 10:
            print(f"Skipping fit estimation for {algorithm}: not enough data")
        else:
            fits = [
                *[ExpFit(algorithm, xdata, ydata)],
                # *[PolyFullFit(algorithm, xdata, ydata)],
                *[PolyFit(algorithm, xdata, ydata, n) for n in range(1, 7)],
                # *[PolyLogFit(algorithm, xdata, ydata, n, m) for n in range(1, 7) for m in range(1, 3)],
            ]

            for ft in sorted(fits, reverse=True, key=lambda ft: ft.r2): #[:3]:
                if ft.r2 >= 0.99:
                    print(ft.title)
            # best_fit = max(fits, key=lambda ft: ft.r2)
            # print(best_fit.title)
            # print(np.diag(best_fit.pcov))

        # best_fit.plot()
        print()

def read_df(infiles: list[Path]):
    return parse_logs([f.read_text() for f in infiles])

def main():
    args = parse_arguments()
    df = read_df(args.infile)
    if args.style == "lines":
        # fit(df)
        table = df[
            (df["size"] == 30) &
            (df["reduction"].isin(("vm_compute", "none")))
        ].groupby(
            ["solver+reduction"]
        )[["wall"]].agg(
            ("mean", "std")
        ).droplevel(axis=1, level=0).sort_values("mean", ascending=False).round(3)
        print(table)
        print(table.to_latex())
        plot_lines(df)
    elif args.style == "cloud":
        plot_cloud(df)

if __name__ == '__main__':
    main()
