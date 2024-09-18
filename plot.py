#!/usr/bin/env python3

import argparse
import re
from typing import Any

import seaborn as sns
from matplotlib import pyplot as plt
import pandas as pd

BENCHMARK_ENTRY = re.compile(
    r"""::[ ]"(?P<experiment>.*?)"[ ]:::[ ]"?(?P<solver>.*?)"?[ ]:::[ ]"?(?P<reduction>.*?)"?[\n]
        (?P<status>solved|timeout)[\n]
        Tactic[ ]call[ ]ran[ ]for[ ](?P<wall>.*?)[ ]secs[ ][(](?P<user>.*?)u,(?P<system>.*?)s[)]""",
    re.VERBOSE
)

SEPARATOR = "-" * 80 + "\n"

def parse_entry(entry_contents: str) -> dict[str, Any]:
    m = BENCHMARK_ENTRY.match(entry_contents)
    # assert m, f"Unparseable entry: {entry_contents}"
    return m.groupdict() if m else None

SOLVER_RENAME = {
    "OL_Reflection_1_base.reduceToAlgo": "OL",
    "OL_Reflection_2_memo.reduceToAlgoMemo": "OL+l",
    "OL_Reflection_3_fmap.reduceToAlgoFmap": "OL+m",
    "OL_Reflection_4_pointers.reduceToAlgoPointers": "OL+m+φ",
    "btauto": "btauto"
}

REDUCTION_RENAME = {
    "none": "",
    "lazy": "+lz",
    "compute": "+c",
    "vm_compute": "+vm",
    "btauto": ""
}

def parse_log(contents: str) -> pd.DataFrame:
    df = pd.DataFrame(
        entry for entry_contents in contents.split(SEPARATOR)
        if entry_contents.strip()
        if (entry := parse_entry(entry_contents))
    )
    # df["solver"] = df["solver"].map(SOLVER_RENAME) # type: ignore
    df["solver"] = df["solver"].map(SOLVER_RENAME)
    df = df[~df["solver"].isin(("OL", "OL+l",))]
    df["solver"] = df["solver"] + df["reduction"].map(REDUCTION_RENAME) # type: ignore
    df["wall"] = pd.to_numeric(df["wall"])
    df["user"] = pd.to_numeric(df["user"])
    df["system"] = pd.to_numeric(df["system"])
    return df

def parse_logs(contents: list[str]) -> pd.DataFrame:
    return pd.concat(parse_log(l) for l in contents)

def plot(df):
    plt.figure(figsize=(12, 8))

    # df = df[df["reduction"].isin(("btauto", "vm_compute"))]
    df = df[df["status"] == "solved"]
    # ax = sns.violinplot(
    # ax = sns.barplot(errorbar="ci",
    ax = sns.lineplot(marker="o",
        data=df, x='experiment', y='wall', hue='solver',
    )
    # ax.set_yscale('log')

    # plt.xticks(rotation=45, ha='right')
    # plt.title('Wall time')
    plt.xlabel('Experiment')
    plt.ylabel('Wall clock time (seconds, log scale)')
    plt.legend(title='Solver')
    plt.tight_layout()

    # Show plot
    plt.show()
    return

def parse_arguments():
    parser = argparse.ArgumentParser(description='Plot Coq-OL benchmark results.')
    parser.add_argument("infile", nargs='+', type=argparse.FileType("r"),
                        help="File to read benchmarks from.")
    return parser.parse_args()

def main():
    args = parse_arguments()
    plot(parse_logs([f.read() for f in args.infile]))

if __name__ == '__main__':
    main()
