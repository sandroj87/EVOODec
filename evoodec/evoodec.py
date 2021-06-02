"""
EVOODec - A deconvolution tool for EVOO abosorption spectra analysis

Author  : Sandro Jurinovich
E-mail  : sandro.jurinovich@posta.istruzione.it
Version : 1.0
Date    : 30/12/2020

"""

# -----------------------------------------------------------------------------
# MODULES
#

# Import Python modules
import os, sys
import numpy as np
from   PIL import Image, ImageTk
from   scipy import interpolate
import matplotlib.pyplot as plt

# Import Tkinter module for GUI
import tkinter as tk
from   tkinter import filedialog

# Matplotlib integration in Tkinter
from matplotlib.backends.backend_tkagg import (
    FigureCanvasTkAgg, NavigationToolbar2Tk)
from matplotlib.backend_bases import key_press_handler
from matplotlib.figure import Figure


# -----------------------------------------------------------------------------
# CLASSES AND FUNCTIONS
#

class EvooDec:

    # Properties of EvooDec class
    VERSION         = "EVOODec - Version 1.0"
    
    # Files
    WORKDIR          = os.getcwd()
    DEF_REF_FILE     = os.path.join(WORKDIR,"data/pigments.csv" )
    REF_FILE         = ''
    DEF_EVOO_FILE    = os.path.join(WORKDIR,"data/evoo_test.CSV")
    EVOO_FILE        = ''
    LOGO             = os.path.join(WORKDIR,"logo.png")

    # Data
    IPRINT           = 2
    CURDIR           = os.getcwd()
    PIGMENTS         = []
    ACTIVE_PIGMENTS  = []
    EVOO_DENSITY     = 0.91  # Density of EVOO (g/ml)
    
    # Flags
    VALID            = True  # Deconvolution
    BASELINE         = False # Apply baseline correction (default False)
    OPLEN            = 1.0   # Optical path length (default 1.0 cm)
    X_MIN            = 0 
    X_MAX            = 0
    DELTA_X          = 1
    N_PIGMENTS       = 0    # Number of pigments used for deconvolution
    MW               = []   # Molecular weights of pigments
    wavelengthExp    = []
    absExp           = []
    X_REF            = []   # Wavelength of reference spectra
    EPS_REF          = []   # Epsilon of reference spectra
    X_EVOO           = []   # Wavelength array of EVOO spectrum
    ABS_EVOO         = []   # Absorption of EVOO spectrum
    ABS_DEC          = []   # Absorption of reconstructed spectrum
    ABS_DEC_CONTR    = []
    X_REF_LIM        = []
    X_EVOO_LIM       = []
    X_SEL_LIM        = []   # Selected limits for x-axis
    COLORS           = ['gray','cyan', 'blue', 'orange', 'red', 'yellow',
                        'pink','brown']
    filename         = ''
    
    # >>> Constructur for EvooDec class
    #
    #
    def __init__(self,master):

        master.title(self.VERSION)
        #master.geometry("1024x800")
        master.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.master = master

        # +++ Create main column layout
        self.left_col = tk.Frame(master)
        self.left_col.grid(row=0,column=0)

        self.rigth_col = tk.Frame(master)
        self.rigth_col.grid(row=0,column=1)
        
        # +++ Create main frames in left column
        self.cmd_frame = tk.LabelFrame(self.left_col,
            text="Step 1: Select input data files",fg="blue",
            borderwidth = 0, highlightthickness = 0)
        self.cmd_frame.grid(row=0,column=0,sticky="N",pady=10,padx=10)
        
        self.opt_frame = tk.LabelFrame(self.left_col,
            text="Step 2: Apply corrections and select spectral window",fg="blue",
            borderwidth = 0, highlightthickness = 0)
        self.opt_frame.grid(row=1,column=0,sticky="NW",pady=10,padx=10)
        
        self.pig_frame = tk.LabelFrame(self.left_col,
            text="Step 3: Select pigments for deconvolution",
            fg="blue",borderwidth = 0, highlightthickness = 0)
        self.pig_frame.grid(row=2,column=0,sticky="NW",pady=10,padx=10)

        self.dec_frame = tk.LabelFrame(self.left_col,
            text="Step 4: Execute deconvolution and get the results!", fg="blue",
            borderwidth = 0, highlightthickness = 0)
        self.dec_frame.grid(row=3,column=0,sticky="NW",pady=10,padx=10)
        
        # +++ Create main frames in right column
        self.plt_frame = tk.Frame(self.rigth_col,
            highlightbackground="black",highlightthickness=1)
        self.plt_frame.grid(row=0,column=0,sticky="NW",pady=10,padx=10,columnspan=2)
      
        self.res_frame = tk.Frame(self.rigth_col)
        self.res_frame.grid(row=1,column=0,sticky="NWE  ",pady=10,padx=10)
        self.res_frame.grid_columnconfigure(0, weight=1)

        self.out_text = tk.Text(self.rigth_col,height=14, width=50)
        self.out_text.grid(row=1,column=1)
        self.out_text.insert(tk.END,"Welcome in EVOO deconvolution program\n")

        # +++ Initzialize tk variables
        self.OPLEN_SEL    = tk.DoubleVar(value=self.OPLEN)
        self.LBL_REF_MIN  = tk.DoubleVar()
        self.LBL_REF_MAX  = tk.DoubleVar()
        self.LBL_REF_PTS  = tk.IntVar()
        self.X_SEL_MIN    = tk.DoubleVar()
        self.X_SEL_MAX    = tk.DoubleVar()
        self.LBL_EVOO_MIN = tk.DoubleVar()
        self.LBL_EVOO_MAX = tk.DoubleVar()
        self.LBL_EVOO_PTS = tk.IntVar()
        self.BASELINE     = tk.BooleanVar()
        
        # Button for selecting reference spectra
        self.btnBrwPure()
        
        # Button for selecting EVOO spectrum
        self.btnBrwEVOO()
        
        # Option panel
        self.optPanel()
        
        # Load input files
        if(self.REF_FILE):  self.loadRef()
        if(self.EVOO_FILE): self.loadEVOO()
        
        # Pigment panel
        self.selPigments()
        
        # Create sliders in selPigments panel
        self.slider = []
        self.CONC_PPM_VAL = []
        row = 1
        # Here we always consider TRIOLEIN as a first spectrum of the list
        for i,p in enumerate(self.PIGMENTS):
            row += 1
            self.CONC_PPM_VAL.append(tk.DoubleVar())
            if(i==0):
                slider = tk.Scale(self.pig_frame,orient=tk.HORIZONTAL,
                length=200, from_=0, to=8E6,resolution=2E4,variable=self.CONC_PPM_VAL[i])
            else:
                slider = tk.Scale(self.pig_frame,orient=tk.HORIZONTAL,
                length=200, from_=0, to=20,resolution=0.1,variable=self.CONC_PPM_VAL[i])
            slider.grid(column=2,row=row)
            self.slider.append(slider)
            self.slider[i].bind("<ButtonRelease-1>", self.changeConc)

        # Textarea
        self.textarea = tk.Text(self.res_frame,height=14,width=35)
        self.textarea.grid(row=0,column=0,sticky="W")
        self.textarea.insert(tk.END, self.VERSION)
    
        # Execute button
        self.btnExe()       # Button for executing deconvolution

    # -------------------------------------------------------------------------   
        
    # >>> Event handler for sliders
    def changeConc(self,event):
        concppm = []
        for i,p in enumerate(self.PIGMENTS):
            concppm.append(float(self.slider[i].get()))
        concppm = np.array(concppm)
        X_REF,EPS_REF,X_EVOO,ABS_EVOO = self.processSpectra()
        ABS_CALC_CONTR = EPS_REF * (concppm*self.EVOO_DENSITY/(self.MW*1000))
        ABS_CALC       = np.sum(ABS_CALC_CONTR,axis=1)
        #print(ABS_CALC)
        FILTER = np.ones(len(self.PIGMENTS),dtype=bool)
        self.printResults(ABS_EVOO,ABS_CALC,self.PIGMENTS,concppm,'MANUAL FITTING')
        self.plot(X_EVOO,ABS_EVOO,FILTER,X_REF,EPS_REF,ABS_CALC,ABS_CALC_CONTR)

    # >>> Close window
    def on_closing(self):
        if tk.messagebox.askokcancel("Quit", "Do you want to quit?"):
            master.destroy()
            sys.exit()

    # >>> Create button for loading reference compounds spectra
    def btnBrwPure(self):
        
        button = tk.Button(self.cmd_frame,text="Load pigments data", 
            command = self.fileDialogRef, width=20)
        button.grid(column = 0, row = 0, pady=2)
        
        # Set default value
        if(self.REF_FILE == '' and self.DEF_REF_FILE != ''): 
            self.REF_FILE = self.DEF_REF_FILE
            txt    = os.path.basename(self.REF_FILE)
            txtcol = "green"
        else:
            txt    = "Please select file of pure compounds spectra"
            txtcol = "red"
            
        self.labelFileRef = tk.Label(self.cmd_frame,text=txt,
            width=35,anchor='w',fg=txtcol)
        self.labelFileRef.grid(column = 1, row = 0, pady=2, padx=2)
        
        pass
    
    
    # >>> Create button for loading EVOO spectrum
    def btnBrwEVOO(self):
        
        txt = "Load EVOO spectrum"
        button = tk.Button(self.cmd_frame,text=txt, 
            command = self.fileDialogEVOO, width=20)
        button.grid(column = 0, row = 1, pady=2)
        
        # Set default value
        if(self.EVOO_FILE == '' and self.DEF_EVOO_FILE != ''): 
            self.EVOO_FILE = self.DEF_EVOO_FILE
            txt    = os.path.basename(self.EVOO_FILE)
            txtcol = "green"
        else:
            txt    = "Please select file of EVOO spectrum"
            txtcol = "red"

        self.labelFileEVOO = tk.Label(self.cmd_frame,text=txt,
            width=35,anchor='w',fg=txtcol)
        self.labelFileEVOO.grid(column = 1, row = 1, pady=2, padx=2)
        
        pass
    
    
    # >>> Open file dialog for selecting spectra of pure compounds
    def fileDialogRef(self):
        self.REF_FILE = filedialog.askopenfilename(
            initialdir = self.CURDIR+"/", title = "Select a file", 
            filetypes=(("CSV (;)","*.csv"),("All files","*.*")))
        fname = os.path.basename(self.REF_FILE)
        self.labelFileRef.configure(text = fname, fg="green")
        self.loadRef()
        pass
       
        
    # >>> Open file dialog for selecting spectra of EVOO  
    def fileDialogEVOO(self):
        self.EVOO_FILE = filedialog.askopenfilename(
            initialdir = self.CURDIR+"/", title = "Select a file", 
            filetypes=(("CSV (;)","*.csv"),("All files","*.*")))
        fname = os.path.basename(self.EVOO_FILE)
        self.labelFileEVOO.configure(text = fname, fg="green")
        self.loadEVOO()
        pass


    # >>> Load file for pure compounds
    def loadRef(self):
        out = '\nLoading reference file: %s' % os.path.basename(self.REF_FILE)
        print(out)
        self.out_text.insert(tk.END,out)
        self.out_text.see(tk.END)
        
        # Load absorption spectra from CSV file ";" separated
        # First column  : wavelength(nm)
        # Other columns : molar extinsion coefficient (M^-1cm-1)
        # First line    : Pigment name
        # Second line   : molecular weight
        # Lines starting with '#' will be treated as comments
        #
        ind      = 0
        comments = ''
        data     = []
        with open(self.REF_FILE,'r') as f:
            while(True):
                line = f.readline()
                if not line: break
                # Skip comment lines
                if(line[0] != '#'):
                    # 1st line -> pigment names
                    if(ind==0):
                        pigments = line.split(';')[1:]
                        pigments = [xx.strip(' \n\t\r') for xx in pigments]
                        ind += 1
                        continue
                    # 2nd line -> molecular weights
                    if(ind==1):
                        MW = line.split(';')[1:]
                        #print(MW)
                        MW = np.array([float(x) for x in MW])
                        ind += 1
                        continue
                    # Read data lines
                    data += [line.split(';')]
                else:
                    comments += line.strip("#")
        data = np.array(data,dtype=float)

        # Check the file consistency -> TO BE DONE        
        msg = "\nReference file correctly loaded!"
        
        self.X_REF    = data[:,0]    # First column is wavelength
        self.EPS_REF  = data[:,1:]   # Other column are epsilon
        self.PIGMENTS = pigments
        self.MW       = MW
        
        self.X_REF_LIM = np.array([np.min(data[:,0]),np.max(data[:,0])])
        
        self.LBL_REF_MIN.set(round(self.X_REF_LIM[0],1))
        self.LBL_REF_MAX.set(round(self.X_REF_LIM[1],1))
        
        self.LBL_REF_PTS.set(len(self.X_REF))

        # Reload pigment checkbox
        self.selPigments()
        pass
       
        
    # >>> Load file for EVOO
    def loadEVOO(self):
        out = '\nLoading EVOO      file: %s' % os.path.basename(self.EVOO_FILE)
        print(out)
        self.out_text.insert(tk.END,out)
        self.out_text.see(tk.END)
        
        # Load file using np.genfromtxt function
        # File structure: csv file ; separated
        # 1st col: wavelength (nm)
        # 2nd col: absorbance
        evoo_data = np.genfromtxt(self.EVOO_FILE,delimiter=';',
             comments='#',encoding='utf-8-sig')
             
        # Check file integrity
        dim = np.shape(evoo_data)[1]
        if(dim < 2):
            msg = "\nEVOO file must contain at least two columns!"
            self.VALID = False
        elif(dim > 2):
            msg =  "\nEVOO file contains %d columns!\n" % dim
            msg += "Only the first two cols will be considered"
            
        else:
            msg = "\nEVOO file correctly loaded!"
        
        self.X_EVOO   = evoo_data[:,0]
        self.ABS_EVOO = evoo_data[:,1]
        
        self.X_EVOO_LIM = np.array([np.min(evoo_data[:,0]),np.max(evoo_data[:,0])])
        
        self.X_SEL_MIN.set(round(self.X_EVOO_LIM[0],1))
        self.X_SEL_MAX.set(round(self.X_EVOO_LIM[1],1))
        
        self.LBL_EVOO_MIN.set(round(self.X_EVOO_LIM[0],1))
        self.LBL_EVOO_MAX.set(round(self.X_EVOO_LIM[1],1))
        
        self.LBL_EVOO_PTS.set(len(self.X_EVOO))
        
        self.plot(self.X_EVOO,self.ABS_EVOO)
        
        pass        
    
    
    # >>> optPanel
    def optPanel(self):

        # Optical path length
        tk.Label(self.opt_frame,text="Optical path length").grid(row=0,column=0,sticky='W')
        tk.Entry(self.opt_frame,textvariable=self.OPLEN_SEL,width=10,justify='center').grid(row=0,column=2)
        tk.Label(self.opt_frame,text="cm").grid(row=0,column=3,sticky='W')
        
        # Checkbox for baseline correction
        tk.Label(self.opt_frame,text="Apply baseline correction").grid(row=1,column=0,sticky='W')
        tk.Checkbutton(self.opt_frame,variable=self.BASELINE).grid(row=1,column=2,sticky="W")

        # Table for spectral window
        tk.Label(self.opt_frame,text="Start (nm)").grid(row=3,column=0,sticky='W')
        tk.Label(self.opt_frame,text="End (nm)").grid(row=4,column=0,sticky='W')
        tk.Label(self.opt_frame,text="Points").grid(row=5,column=0,sticky='W')
        
        # Reference data
        tk.Label(self.opt_frame,text="Reference").grid(row=2,column=1)
        tk.Label(self.opt_frame,textvariable=self.LBL_REF_MIN).grid(row=3,column=1)
        tk.Label(self.opt_frame,textvariable=self.LBL_REF_MAX).grid(row=4,column=1)
        tk.Label(self.opt_frame,textvariable=self.LBL_REF_PTS).grid(row=5,column=1)

        # EVOO default
        tk.Label(self.opt_frame,text="EVOO (file)").grid(row=2,column=2)
        tk.Label(self.opt_frame,textvariable=self.LBL_EVOO_MIN).grid(row=3,column=2)
        tk.Label(self.opt_frame,textvariable=self.LBL_EVOO_MAX).grid(row=4,column=2)
        tk.Label(self.opt_frame,textvariable=self.LBL_EVOO_PTS).grid(row=5,column=2)
        
        # EVOO data
        tk.Label(self.opt_frame,text="EVOO (proc)").grid(row=2,column=3)
        tk.Entry(self.opt_frame,textvariable=self.X_SEL_MIN,width=10,justify='center').grid(row=3,column=3)
        tk.Entry(self.opt_frame,textvariable=self.X_SEL_MAX,width=10,justify='center').grid(row=4,column=3)
        tk.Label(self.opt_frame,textvariable=self.LBL_EVOO_PTS).grid(row=5,column=3)

        # Button process spectra  
        btn = tk.Button(self.opt_frame,text="PREVIEW",command=self.btnProcSpec)
        btn.grid(row=6,column=3,pady=2)

        # Button to reset        
        btn = tk.Button(self.opt_frame,text="RESET",command=self.btnRst)
        btn.grid(row=6,column=2,pady=2)
        
        pass
    
    # >>> Reset button
    def btnRst(self):
        print("Reset default")
        self.out_text.insert(tk.END,"\nReset EVOO spectrum to original\n")
        #self.OPLEN_SEL.set(self.OPLEN)
        self.out_text.see(tk.END)
        self.X_SEL_MIN.set(round(self.X_EVOO_LIM[0],1))
        self.X_SEL_MAX.set(round(self.X_EVOO_LIM[1],1))
        self.btnProcSpec()
        for i,p in enumerate(self.PIGMENTS):
            self.slider[i].set(0)
        self.textarea.delete('1.0', tk.END)
        self.textarea.insert(tk.END,self.VERSION)
        pass  
    
    
    # >>> Call function bind to button process
    def btnProcSpec(self):
        X_REF,EPS_REF,X_EVOO,ABS_EVOO = self.processSpectra()
        self.plot(X_EVOO,ABS_EVOO,None,X_REF,EPS_REF)
        pass  
    
  
    # >>> Function to check integrety of spectra
    def processSpectra(self):
        
        warn   = ''

        # Pre process spectra
        print("\n\nPre-process spectra ...")
        self.out_text.insert(tk.END, '\nPre processing-spectra\n')
        X_SEL_MIN = self.X_SEL_MIN.get()
        X_SEL_MAX = self.X_SEL_MAX.get()
        
        # Check consistency of selected EVOO spectrum limits
        if(X_SEL_MIN > X_SEL_MAX):
            warn += "X_EVOO_MIN %4d > X_EVOO_MAX %d\n" % (X_SEL_MIN,X_SEL_MAX)
            self.X_SEL_MIN.set(self.X_EVOO_LIM[0])
            X_SEL_MIN = self.X_EVOO_LIM[0]
        if(X_SEL_MAX < X_SEL_MIN):
            warn += "X_EVOO_MAX %4d < X_EVOO_MIN %d\n" % (X_SEL_MAX,X_SEL_MIN)
            self.X_SEL_MAX.set(self.X_EVOO_LIM[1])
            X_SEL_MAX = self.X_EVOO_LIM[1]

        ind1 = np.argwhere(self.X_EVOO >= X_SEL_MIN).flatten()
        ind2 = np.argwhere(self.X_EVOO <= X_SEL_MAX).flatten()
        ind  = np.intersect1d(ind1,ind2)        

        X_EVOO   = self.X_EVOO[ind]
        ABS_EVOO = self.ABS_EVOO[ind]

        X_REF    = self.X_REF
        EPS_REF  = self.EPS_REF

        # Extract number of points (x-axis)
        NPT_EVOO = np.shape(ABS_EVOO)[0]
        NPT_REF  = np.shape(EPS_REF)[0]
        self.LBL_EVOO_PTS.set(NPT_EVOO)

        # Compute steps
        X_EVOO_STEP = (X_SEL_MAX-X_SEL_MIN)/(NPT_EVOO-1)
        X_REF_STEP  = (self.X_REF_LIM[1]-self.X_REF_LIM[0])/(NPT_REF-1)
        
        table  =  '\n'
        table += '\n                PURE  EVOO\n'
        table += '     ---------------------\n'
        table += '     X_MIN    = %4d  %4d\n' % (self.X_REF_LIM[0],X_SEL_MIN)
        table += '     X_MAX    = %4d  %4d\n' % (self.X_REF_LIM[1],X_SEL_MAX)
        table += '     X_POINTS = %4d  %4d\n' % (NPT_REF,NPT_EVOO)
        table += '     DELTA_X  = %4.1f  %4.1f\n' % (X_REF_STEP,X_EVOO_STEP)
        table += '     ---------------------\n'
        
        print(table)

        if(X_REF_STEP != X_EVOO_STEP):
            warn += "Different resolution between reference pigments and EVOO files\n"
        
        # Check on minimum
        if(X_SEL_MIN < self.X_REF_LIM[0]):
            warn += "X_EVOO_MIN %4d < X_REF_MIN %4d\n" % (X_SEL_MIN,self.X_REF_LIM[0])
            ind = np.argwhere(X_EVOO >= self.X_REF_LIM[0]).flatten()
            X_EVOO   = X_EVOO[ind]
            ABS_EVOO = ABS_EVOO[ind]
            self.X_SEL_MIN.set(self.X_REF_LIM[0]) 
        elif(X_SEL_MIN > self.X_REF_LIM[0]):
            warn += "X_EVOO_MIN %4d > X_REF_MIN %4d\n" % (X_SEL_MIN,self.X_REF_LIM[0])
            ind = np.argwhere(X_REF >= X_SEL_MIN).flatten()
            X_REF    = X_REF[ind]
            EPS_REF  = EPS_REF[ind]
        
        # Check on maximum
        if(X_SEL_MAX > self.X_REF_LIM[1]):
            warn += "X_EVOO_MAX %4d > X_REF_MAX %4d\n" % (X_SEL_MAX,self.X_REF_LIM[1])
            ind = np.argwhere(X_EVOO <= X_SEL_MAX).flatten()
            X_EVOO   = X_EVOO[ind]
            ABS_EVOO = ABS_EVOO[ind]
            self.X_SEL_MAX.set(self.X_REF_LIM[1])
        elif(X_SEL_MAX < self.X_REF_LIM[1]):
            warn += "X_EVOO_MAX %4d < X_REF_MAX %4d\n" % (X_SEL_MAX,self.X_REF_LIM[1])
            ind = np.argwhere(X_REF <= X_SEL_MAX).flatten()
            X_REF    = X_REF[ind]
            EPS_REF  = EPS_REF[ind]
        
        # Interpolate EVOO spectrum if needed
        if(warn != ''):
            print(warn)
            print("\nInterpolating EVOO spectrum to match the pure compound x-axis ...")
            f = interpolate.interp1d(X_EVOO, ABS_EVOO,fill_value='extrapolate',kind='cubic')
            ABS_EVOO = f(X_REF)
            self.out_text.insert(tk.END, 'Warning!\n'+warn)
            self.out_text.see(tk.END)
        else:
            print("Spectra are OK")
            self.out_text.insert(tk.END, 'Spectra are OK!\n')
            self.out_text.see(tk.END)

        # Correct the absorbance for the optical path length
        self.out_text.insert(tk.END, ' ... optical path length %3.1f cm\n' % self.OPLEN_SEL.get())
        if(self.OPLEN_SEL.get() != 1.0):
            self.out_text.insert(tk.END, '     -> normalize to 1.0\n')
            ABS_EVOO = ABS_EVOO/self.OPLEN_SEL.get()

        # Apply baseline correction
        if(self.BASELINE.get() is True):
            print("Apply baseline correction")
            print("Minimum value found: %6.2f" % np.min(ABS_EVOO) )
            ABS_EVOO -= np.min(ABS_EVOO)
            self.out_text.insert(tk.END, "Apply baseline correction\n")
            self.out_text.insert(tk.END, "EVOO spectrum will be shifted by %6.2f ABS unit" %  np.min(ABS_EVOO))
            self.out_text.see(tk.END)

        return(X_REF,EPS_REF,X_EVOO,ABS_EVOO)


    # Checkbox for pigment selection to be used in deconvolution
    def selPigments(self):
        row = 1
        self.ACTIVE_PIGMENTS = []
        for i,p in enumerate(self.PIGMENTS):
            # Checkbox
            label = "%s (%8.2f g/mol)" % (p,self.MW[i])
            self.ACTIVE_PIGMENTS.append(tk.BooleanVar())
            row += 1 
            check = tk.Checkbutton(self.pig_frame,text=label, 
                                   variable = self.ACTIVE_PIGMENTS[i])
            check.select()
            check.grid(column = 0,row=row,sticky="W")
            label = tk.Label(self.pig_frame,width=2,bg=self.COLORS[i])
            label.grid(column = 1,row=row,sticky="W")
        pass

        
    # >>> Button for executing deconvolution
    def btnExe(self):
        txt = "DECONVOLVE"
        button = tk.Button(self.dec_frame,text=txt,
                           command=self.exeDec2,width=30)
        button.grid(column=0,row=0,pady=10,padx=10)

        
    
    # >>> TEST Execute Deconvolution 2
    def exeDec2(self):
        
        print("Check spectra...")
        X_REF,EPS_REF,X_EVOO,ABS_EVOO = self.processSpectra()
        #self.plot(X_EVOO,ABS_EVOO)
        
        print("Appply pigment filter...")
        FILTER = np.ones(len(self.PIGMENTS),dtype=bool)
        for i,p in enumerate(self.PIGMENTS):
            print(p,self.ACTIVE_PIGMENTS[i].get())
            FILTER[i] = self.ACTIVE_PIGMENTS[i].get()
        #print(FILTER)
        
        # Apply Filter
        print("Call deconvolution function...")
        PIGMENTS = np.array(self.PIGMENTS)[FILTER]
        MW       = np.array(self.MW)[FILTER]
        EPS_REF  = EPS_REF[:,FILTER]
        
        # Execute deconvolution
        #deconvolution = Deconvolution(self,X_REF,EPS_REF,ABS_EVOO,MW)
        concmol = self.deconvolve(X_REF,EPS_REF,ABS_EVOO,MW)
        concppm = concmol*MW*1000/self.EVOO_DENSITY
        #print(concppm)
        # Set sliders values
        j = 0
        for i,p in enumerate(self.PIGMENTS):
            if(FILTER[i]):
                self.slider[i].set(concppm[j])
                j += 1
            else:
                self.slider[i].set(0)
                
        # Compute and plot deconvolved spectrum
        print("\nReconstructing deconvolved spectrum and calculating residues ...")
        ABS_CALC_CONTR = EPS_REF*concmol
        ABS_CALC       = np.einsum('ik,k->i',EPS_REF,concmol)

        self.printResults(ABS_EVOO,ABS_CALC,PIGMENTS,concppm,'AUTO FITTING')
        self.plot(X_EVOO,ABS_EVOO,FILTER,X_REF,EPS_REF,ABS_CALC,ABS_CALC_CONTR)
        
    
    # >>> Plot spectra
    def plot(self,X_EVOO,ABS_EVOO,FILTER=None,X_REF=[],EPS_REF=[],ABS_CALC=[],ABS_CALC_CONTR=[]):
        
        # Graph configuration
        fig = plt.figure(figsize=(7.0,4.5), dpi=100) 
        canvas = FigureCanvasTkAgg(fig,self.plt_frame) 
        canvas.draw() 
        canvas.get_tk_widget().grid(row=7,column=0) 
        toolbar_frame = tk.Frame(self.plt_frame)
        toolbar_frame.grid(row=9,column=0)
        toolbar = NavigationToolbar2Tk(canvas, toolbar_frame) 
        toolbar.update() 
        
        # Adding features to graph
        plt.xlabel('Wavelength (nm)')
        plt.ylabel('Absorbance')
        plt.title('EVOO Deconvolution')
        plt.xlim(np.min(X_EVOO),np.max(X_EVOO))
        plt.ylim(0,np.max(ABS_EVOO)+np.max(ABS_EVOO)*0.05)
        
        # Process experimental EVOO spectrum for plot
        EXP = self.ABS_EVOO                 # as loaded by inpute (no data processing)
        EXP = EXP/self.OPLEN_SEL.get()      # corrected for optical path length (normalization to 1.0 cm)
        EXP = EXP - np.min(self.ABS_EVOO)   # corrected for baseline

        # Plot EVOO spectrum (as Loaded by input and corrected for baseline and optical path length)
        plt.plot(self.X_EVOO,EXP,'.',markersize=3,color = 'gray')
        if len(X_REF): plt.plot(X_REF,ABS_EVOO,'-k',linewidth=0.8,label='EVOO')

        if len(ABS_CALC):
            plt.plot(X_REF,ABS_CALC,'-g',label='Calculated')
            PIGMENTS = np.array(self.PIGMENTS)[FILTER]
            COLORS   = np.array(self.COLORS[0:len(FILTER)])[FILTER]
            for i in range(len(PIGMENTS)):
                plt.plot(X_REF,ABS_CALC_CONTR[:,i],'-k',
                         color=COLORS[i],linewidth=0.8,
                         label='{i}'.format(i=PIGMENTS[i]))

        plt.legend(loc='best')

        # Save data in txt files (to be done...)
        #if(len(ABS_CALC_CONTR) > 0):
        #    out = np.column_stack((X_REF,ABS_CALC_CONTR,ABS_CALC))
        #    np.savetxt('deconvolution.csv',out,fmt="%16.8E",delimiter=";")

        pass
    
    # ------------------------------------------------------------------------
    # Deconvolution function
    #
    def deconvolve(self,X,EPS_REF,ABS_EVOO,MW):

        self.out_text.insert(tk.END,"Executing deconvolution...\n")
        self.out_text.see(tk.END)

        # Determine number of pigments
        N_PIGMENTS   = np.shape(EPS_REF)[1]

        # Compute the overlap matrix
        print("Computing the overlap matrix...")
        ovlp = np.zeros((N_PIGMENTS,N_PIGMENTS))
        for i in range(N_PIGMENTS):
            for j in range(i,N_PIGMENTS):
                prod = np.multiply(EPS_REF[:,i],EPS_REF[:,j])
                ovlp[i,j] = np.trapz(prod,X[::-1])
        ovlp = ovlp+ovlp.T-np.eye(N_PIGMENTS)*np.diag(ovlp)

        # Diagonalize overlap matrix
        print("Diagonalizing the overlap matrix...")
        eigval,eigvec = np.linalg.eigh(ovlp,UPLO='U')

        # Check eigval zero
        check = np.where(eigval==0)[0]
        if(len(check)>0):
            msg = "\nError!\n%d eigenvalues are zero\nDeconvolution is not possibile!\n" % len(check)
            print(msg)
            self.out_text.insert(tk.END, msg)
            self.out_text.see(tk.END)
            return np.zeros(N_PIGMENTS)

        # Compute base for spectra deconvolution
        print("Computing eigenvectors for the new base ...")
        print(np.shape(EPS_REF))
        base = np.einsum('ri,jr->ji',eigvec,EPS_REF)

        # Compute SV coefficient
        print("Computing SV coefficients...")
        gamma = np.zeros(N_PIGMENTS)
        for i in range(N_PIGMENTS):
            gamma[i] = -np.trapz(base[:,i]*ABS_EVOO/eigval[i],X)
        
        # Compute concentration
        print("Computing pigments' concentrations...")
        concmol = np.einsum('k,ik->i',gamma,eigvec)
        
        return concmol

    def printResults(self,ABS_EVOO,ABS_CALC,PIGMENTS,concppm,txt):
        # +++ R^2 fitting
        ave = np.average(ABS_EVOO)
        Rsq = 1-np.sum((ABS_EVOO-ABS_CALC)**2)/np.sum((ABS_EVOO-ave)**2)
        
        # +++ Output printing
        out  = 'Final results:   '+txt+'\n'
        out += 'R-square      = %9.6f\n' % Rsq
        out += '    PIGMENT CONCENTRATION\n'
        out += '-------------------------------\n'

        for i in range(len(PIGMENTS)):
            if (concppm[i] > 1E4):
                out += '%-12s  = ********* mg/kg\n' % (PIGMENTS[i])
            else:
                out += '%-12s  = %9.3f mg/kg\n' % (PIGMENTS[i],concppm[i])
        out += '-------------------------------\n'
        sumindex = np.argwhere(concppm<1E4).flatten()
        out += 'PIGMENT TOTAL = %9.3f mg/kg\n' % np.sum(concppm[sumindex])
        self.textarea.delete("1.0",tk.END)
        self.textarea.insert(tk.END,out)
        pass
        
# -----------------------------------------------------------------------------
# MAIN PROGRAM
#
if __name__ == "__main__":

    master = tk.Tk()
    evoo = EvooDec(master)
    master.mainloop()
    
# -----------------------------------------------------------------------------
# EOF