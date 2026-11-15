import pathlib
import subprocess
import sys
import tempfile
exe=sys.argv[1]
fixtures=pathlib.Path(__file__).parent/'fixtures'
with tempfile.TemporaryDirectory() as directory:
    dest=pathlib.Path(directory)/'out.obj'
    for name,count in [('planar-square',2),('annulus',8),('warped',2)]:
        p=subprocess.run([exe,str(fixtures/(name+'.obj')),str(dest)],capture_output=True,text=True)
        assert p.returncode==0,(name,p.stderr)
        text=dest.read_text()
        assert sum(line.startswith('f ') for line in text.splitlines())==count,text
        p=subprocess.run([exe,str(fixtures/(name+'.obj')),str(dest)],capture_output=True,text=True)
        assert p.returncode==0 and dest.read_text()==text
    # Exactly distinct close sheets must survive assembled 3D auditing.
    generated=pathlib.Path(directory)/'generated.obj'
    z=format(2.**-1000,'.17g')
    generated.write_text('v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\n'+
        f'v 0 0 {z}\nv 1 0 {z}\nv 1 1 {z}\nv 0 1 {z}\nf 1 2 3 4\nf 5 6 7 8\n')
    p=subprocess.run([exe,str(generated),str(dest)],capture_output=True,text=True)
    assert p.returncode==0,p.stderr
    assert sum(line.startswith('f ') for line in dest.read_text().splitlines())==4
    # Reversed input winding is retained in the written OBJ.
    generated.write_text('v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 4 3 2 1\n')
    p=subprocess.run([exe,str(generated),str(dest)],capture_output=True,text=True)
    assert p.returncode==0,p.stderr
    vertices=[]
    for line in dest.read_text().splitlines():
        words=line.split()
        if words and words[0]=='v':vertices.append(tuple(map(float,words[1:])))
        if words and words[0]=='f':
            a,b,c=[vertices[int(x)-1] for x in words[1:]]
            assert (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])<0
    # Shared seams between planar patches of a warped surface stay fixed.
    generated.write_text('v 0 0 0\nv 1 0 0\nv 1 1 1\nv 0 1 0\nf 1 2 3\nf 1 3 4\n')
    p=subprocess.run([exe,'--target-count','32','--subdivide-boundary','--max-passes','1',
        '--max-edits','2','--max-candidates','16',str(generated),str(dest)],capture_output=True,text=True)
    assert p.returncode in (0,4),p.stderr
    seam=0
    for line in dest.read_text().splitlines():
        words=line.split()
        if words and words[0]=='f':
            ids=[int(x)-1 for x in words[1:]]
            seam+=sum({ids[i],ids[(i+1)%3]}=={0,2} for i in range(3))
    assert seam==2
    dest.write_text('preserve existing destination')
    p=subprocess.run([exe,'--planar',str(fixtures/'warped.obj'),str(dest)],capture_output=True,text=True)
    assert p.returncode!=0 and dest.read_text()=='preserve existing destination'
    bad=pathlib.Path(directory)/'bad.obj'
    for text in [
        'v 0 0 0\nv 2 0 0\nv 0 2 0\nv .25 .25 0\nv 1 .25 0\nv .25 1 0\nf 1 2 3\nf 4 5 6\n',
        'v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\nf 1 2 3\n',
        'v 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 999\n',
        'v nan 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n',
        'v inf 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n',
        'v 1e9999 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n']:
        bad.write_text(text)
        p=subprocess.run([exe,str(bad),str(dest)],capture_output=True,text=True)
        assert p.returncode!=0,(text,p.stderr)
        assert dest.read_text()=='preserve existing destination'
print('OBJ merging, holes, warped surface, determinism and rejection checks passed')
