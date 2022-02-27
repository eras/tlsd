from setuptools import setup

setup(
    name='tlsd',
    version='0.1.0',
    author='Erkki Seppälä',
    author_email='flux@inside.org',
    packages=['tlsd'],
    scripts=[],
    url='http://pypi.python.org/pypi/tlsd/',
    license='LICENSE.MIT',
    description='Tool for generating sequence diagrams from TLC state traces',
    long_description=open('README.md').read(),
    install_requires=[
        "drawSvg==1.8.3",
        "pillow==5.4.1"
    ],
)
